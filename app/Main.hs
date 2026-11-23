{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Data.List (singleton, stripPrefix)
import Control.Arrow (first, Arrow ((***)))

import System.IO (hPutStr, hClose, hIsEOF, hGetLine, hFlush, hSetFileSize, SeekMode (AbsoluteSeek), hSeek)
import System.IO.Temp (withSystemTempFile)
import System.Environment (getArgs, getProgName)
import System.Process (createProcess, std_out, waitForProcess, proc, StdStream(..))
import Control.Monad (join)

import Data.Char (isSpace)
import Data.Maybe (isJust)
import Control.Applicative ((<|>))

class ToDimacs a where
    toDimacs :: a -> String

class ToCNF t where
    toCnf :: t a -> CNF a

data Lit a = Pos a
           | Neg a
    deriving (Eq, Show, Foldable)
unLit :: Lit a -> a
unLit (Pos p) = p
unLit (Neg p) = p

newtype Clause a = Clause { clause :: [Lit a] }
    deriving (Eq, Show, Functor, Foldable, Semigroup, Monoid)

newtype CNF a = CNF { cnf :: [Clause a] }
    deriving (Eq, Show, Functor, Foldable, Semigroup, Monoid)

newtype ElementaryConjunction a = ElemConj { elemConj :: [Lit a] }
    deriving (Eq, Show, Functor, Semigroup, Monoid)

newtype DNF a = DNF { dnf :: [ElementaryConjunction a] }
    deriving (Eq, Show, Functor, Semigroup, Monoid)

data Color = White | Black
    deriving (Eq, Show, Enum, Bounded)

data Layer = LWhite | LBlack | LSum Int Color
    deriving (Eq, Show)

data BoardCoord l = BoardCoord
    { size :: Int
    , layer_count :: Int
    , forward_map :: l -> Int
    , backward_map :: Int -> l
    }

data GlucoseLineOutput = Comment String
                   | SATState Bool
                   | WhiteSpace
                    deriving (Show)

data GlucoseRun = GlucoseRun
                { satState :: Bool
                , found_model :: Maybe [Lit Int]
                }
                deriving (Show)

class BoardEncodeDecode l where
    encode :: (BoardCoord l) -> Int -> Int -> l -> Int
    decode :: (BoardCoord l) -> Int -> (Int, Int, l)

    encode bc x y l
        | x < 0 || x >= size bc = error $ "Invalid x: " ++ show x
        | y < 0 || y >= size bc = error $ "Invalid y: " ++ show y
        | forward_map bc l < 0 || forward_map bc l >= layer_count bc = error $ "Invalid layer: " ++ show (forward_map bc l)
        | otherwise = (forward_map bc l * (size bc) + x) * (size bc) + y
    decode bc z = let (lx, y) = divMod z $ size bc
                      (l, x) = divMod lx $ size bc
                   in (x, y, backward_map bc l)

instance Functor Lit where
    fmap f (Pos a) = Pos $ f a
    fmap f (Neg a) = Neg $ f a

instance BoardEncodeDecode Layer

instance ToDimacs (Lit Int) where
    toDimacs (Pos i) = show i
    toDimacs (Neg i) = '-' : show i

dimacsHeader :: Int -> Int -> String
dimacsHeader p_count clause_count = "p cnf " <> show p_count <> " " <> show clause_count

instance ToDimacs (Clause Int) where
    toDimacs  = foldr (\lit acc -> toDimacs lit ++ (' ' : acc)) "0" . clause

instance ToDimacs (CNF Int) where
    toDimacs  = foldr (\c acc -> toDimacs c ++ ('\n' : acc)) "" . cnf

instance ToCNF ElementaryConjunction where
    toCnf = CNF . map (Clause . singleton) . elemConj

instance ToCNF DNF where
    toCnf = CNF . map Clause . sequence . map elemConj . dnf

colToLayer :: Color -> Layer
colToLayer White = LWhite
colToLayer Black = LBlack

otherCol :: Color -> Color
otherCol White = Black
otherCol Black = White

makeBoardCoord :: Int -> Int -> BoardCoord Layer
makeBoardCoord n k = BoardCoord
    { size = n
    , layer_count = lc
    , forward_map = \case LWhite -> 0
                          LBlack -> 1
                          LSum x c -> 2 + k'*(fromEnum c) + x
    , backward_map = \case 0 -> LWhite
                           1 -> LBlack
                           x -> let x' = x - 2
                                    (c, x'') = first toEnum $ divMod x' k'
                                 in LSum x'' c
    }
  where
    k' = k + 2 -- + 2 accounts for LSum (k + 1) and for LSum 0
    lc = 2 + 2*(k')

encodeNxNQueen :: Int -> Int -> CNF (Int, Int, Layer)
encodeNxNQueen n k = noSameSpot <> foldl' (\acc f -> f White <> f Black <> acc) mempty [sums, kOfColor] <> allSafe
  where
    -- for all. x,y (encode x y White) != (encode x y Black) .. in truth values
    -- w = encode x y White
    -- b = encode x y White
    -- (w and not b) or (not w and b)
    -- (w or not w) and (w or b) and (not b or not w) and (not b or b)
    -- (w or b) and (not b or not w)
    noSameSpot = CNF [ Clause $ map (Neg . (x,y,)) [LWhite, LBlack]
                     | x <- [0..(n - 1)], y <- [0..(n - 1)] ]
    -- exactly k tiles of color c are true
    -- k-clenna podmnozina [k]x[k] sjednocena na and <- DNF encoding, prevod na CNF exponencialni, mozna existuje lepsi reseni
    -- kOfColor c = toCnf $ DNF $ map (ElemConj . map (Pos . uncurry (flip flip c . encode bc))) $ subsets k [ (x, y) | x <- [0..(n - 1)], y <- [0..(n - 1)] ]
    --
    -- better version using `sums`:
    -- end_x,end_y,LSum k is true and end_x,end_y,LSum K+1 is false
    kOfColor c = CNF [Clause [Pos ((n - 1), (n - 1), LSum k c)], Clause [Neg ((n - 1), (n - 1), LSum (k + 1) c)]]

    -- encodes that at x,y,(LSum z) the number of variables <x,<y,{LWhite,LBlack} is at least z
    -- x,y,(LSum z) <- (x,y)-1,(LSum z) or ((x,y)-1,(LSum z - 1) and (x,y),{LWhite|LBlack})
    --    .... (x,y)-1 je predchozi policko, tj. (x-1),y iff x!= 0, jinak (n-1),y-1, base case: x,y = 0,0 plati jen pro LSum 0
    -- split into two: 1) x,y,(LSum z) <- (x,y)-1,LSum(z), and
    --                 2) x,y,(LSum z) <- ((x,y)-1,(LSum z - 1) and ((x,y),LWhite or (x,y),LBlack))
    --  1) w <- z = w or not z
    --  2) propagation <- (previous_prop and (white or black)) = propagation or not (previous_prop and (white or black)) =
    --     = propagation or not previous_prop or not (white or black) = propagation or (not previous_prop or (not white and not black)) =
    --     = propagation or ((not previous_prop or not white) and (not previous_prop or not black)) =
    --     = (propagation or not previous_prop or not white) and (propagation or not previous_prop or not black)
    -- also need the other diction so it's an iff, not just <-, i.e. x,y,(LSum z) -> (x,y)-1,(LSum z) or ((x,y)-1,(LSum z - 1) and (x,y),{LWhite|LBlack})
    --                                                                  W         ->    X             or     Y                 and       Z
    --  3) not W or (X or (Y and Z)) = (not W or X) or (Y and Z) = (not W or X or Y) and (not W or X or Z)
    sums c = CNF [ Clause [Pos (0, 0, LSum 0 c)]
                 , Clause [Neg (0, 0, LSum 1 c), Pos (0, 0, colToLayer c)] -- these two encode the case if a queen is on (0,0)
                 , Clause [Pos (0, 0, LSum 1 c), Neg (0, 0, colToLayer c)] --
                 ]
          <> CNF [ Clause [Neg (0, 0, LSum z c)] -- propagate 0,0,LSum z>=2 is false
                 | z <- [2..k+1] ]
          <> encodeNext 0 0
      where
        encodeRule1 x y prev_x prev_y = CNF [ Clause [Pos (x, y, LSum z c), Neg (prev_x, prev_y, LSum z c)]
                                            | z <- [0..k+1] ]
        encodeRule2 x y prev_x prev_y = CNF [ Clause [ Pos (x, y, LSum z c)
                                                     , Neg (prev_x, prev_y, LSum (z - 1) c)
                                                     , Neg (x, y, colToLayer c)
                                                     ]
                                            | z <- [1..k+1] ]
        encodeRule3 x y prev_x prev_y = CNF $ mconcat [ [ Clause [ prop z
                                                                 , prev_prop z
                                                                 , Pos (prev_x, prev_y, LSum (z - 1) c)
                                                                 ]
                                                        , Clause [ prop z
                                                                 , prev_prop z
                                                                 , Pos (x, y, colToLayer c)
                                                                 ]
                                                        ]
                                                      | z <- [1..k+1] ]
           where
             prop z = Neg (x, y, LSum z c)
             prev_prop z = Pos (prev_x, prev_y, LSum z c)
        encodeNext x y = case advance x y of
                            Just (next_x, next_y) -> mconcat $ encodeNext next_x next_y : map (\f -> f next_x next_y x y) [encodeRule1, encodeRule2, encodeRule3]
                            Nothing -> CNF []
        advance x y
            | x + 1 < n = Just (x + 1, y)
            | y + 1 < n = Just (0, y + 1)
            | otherwise = Nothing

    allSafe :: CNF (Int,Int,Layer)
    allSafe = mconcat [ safe x y c | x <- [0..n-1], y <- [0..n-1], c <- [White, Black] ]

    -- if x,y,c, then diagonals + x row + y column all are false for the other color
    -- A = x,y,c
    -- 1) A -> row
    --  = not A or (row)
    --  row = not 0,y,!c and not 1,y,!c .... and not (n -1),y,!c ... excluding not x,y,!c (since that's true via noSameSpot)
    --  = not A or (not 0,y,!c and not 1,y,!c .... and not (n -1),y,!c)
    --  = (not A or not 0,y,!c) and (not A or not 1,y,!c) and ... and (not A or not (n - 1),y,!c)
    -- 2) A -> column
    --    = not A or (column)
    --    = not A or (not x,0,!c and not x,1,!c and ... and not x,(n - 1),!c) ... excluding x,y,!c
    --    = (not A or not x,0,!c) and ... and ... (not A or not x,(n - 1), !c)
    -- 3) A -> diagonals = A -> (diagonal to top left and diagonal to bottom left and diagonal to top right and diagonal to botom right)
    -- 3.1) A -> diagonal to top left
    --      = not A or (not (x-1),(y-1),!c and ... until 0,0,!c)
    -- 3.2) A -> diagonal to bottom left
    --      = not A or (not (x-1),(y+1),!c and ... until 0,(n-1),!c)
    -- 3.3) A -> diagonal to top right
    --      = not A or (not (x+1),(y-1),!c and ... until (n - 1),0,!c)
    -- 3.4) A -> diagonal to bottom right
    --      = not A or (not (x+1),(y+1),!c and ... until (n - 1),(n - 1),!c)
    safe x y c = row <> column <> mconcat [ diag dx dy xLim yLim
                                          | dx <- [1, -1], dy <- [1, -1]
                                          | xLim <- [(n - 1), 0], yLim <- [(n - 1), 0] ]
      where
        c' = colToLayer c
        otherC = otherCol c
        otherC' = colToLayer otherC
        notA = Neg (x, y, c')

        row = CNF [ Clause [notA, Neg (x', y, otherC')] | x' <- [0..(n - 1)], x' /= x ]
        column = CNF [ Clause [notA, Neg (x, y', otherC')] | y' <- [0..(n - 1)], y' /= y ]
        diag dx dy xLim yLim = CNF [ Clause [ notA, Neg (x', y', otherC') ]
                                   | x' <- drop 1 [x,x+dx..xLim]
                                   | y' <- drop 1 [y,y+dy..yLim] ]

fullDimacs :: CNF Int -> String
fullDimacs cnf_expr = dimacsHeader (maximum cnf_expr) (length $ cnf cnf_expr) <> ('\n' : toDimacs cnf_expr)

generateEncoding :: Int -> Int -> String
generateEncoding n k = fullDimacs $ fmap (\(x,y,l) -> 1 + encode bc x y l) $ encodeNxNQueen n k
  where
    bc = makeBoardCoord n k

runGlucose :: String -> a -> (String -> a -> a) -> IO a
runGlucose input initial_state reader = do
    (_, Just hStdout, _, hProcess) <- createProcess (proc "./glucose-syrup" [input]){ std_out = CreatePipe }

    let loop state = do
                        eof <- hIsEOF hStdout
                        if eof
                            then return state
                            else hGetLine hStdout >>= loop . flip reader state
    final_state <- loop initial_state
    hClose hStdout
    _ <- waitForProcess hProcess
    return final_state


parseGlucose :: String -> Maybe GlucoseRun -> Maybe GlucoseRun
parseGlucose line prev_state = case parseGlucoseLine line of
    SATState state -> maybe (pure $ GlucoseRun state Nothing) (\s -> pure $ s {satState = state}) prev_state
    Comment _ -> prev_state
    WhiteSpace -> prev_state
  where
    parseGlucoseLine :: String -> GlucoseLineOutput
    parseGlucoseLine ('c':xs) = Comment $ dropWhile isSpace xs
    parseGlucoseLine ('s':xs) = SATState $ isJust $ stripPrefix "SATISFIABLE" $ dropWhile isSpace xs
    parseGlucoseLine _ = WhiteSpace

solve :: Int -> IO (Maybe Int)
solve n = withSystemTempFile "encoding.cnf" $ curry (maxK . uncurry solvers)
  where
    maxK = foldr (\r acc -> r >>= maybe (pure Nothing)
                                        ((<$> acc) . flip (<|>) . Just))
                (pure Nothing)

    solvers pathEncoding hEncoding = map (solver pathEncoding hEncoding) [1..]
    solver pathEncoding hEncoding k = do
        putStrLn $ "trying k=" <> show k
        hSeek hEncoding AbsoluteSeek 0
        hSetFileSize hEncoding 0
        hPutStr hEncoding $ generateEncoding n k
        hFlush hEncoding

        run <- runGlucose pathEncoding Nothing parseGlucose
        pure $ case run of
            Nothing -> Nothing
            Just (GlucoseRun {satState = False}) -> Nothing
            Just _ -> Just k

main :: IO ()
main = getArgs
    >>= \case ["check", n_str, k_str] -> do
                let (n,k) = join (***) (read @Int) (n_str, k_str)
                putStr $ generateEncoding n k
              ["solve", n_str] -> solve (read @Int n_str) >>= print
              _ -> getProgName >>= putStr . usage
  where
    usage arg0 = unlines
        [ "USAGE: " <> arg0 <> " [COMMAND]"
        , ""
        , "COMMANDS:"
        , "\tcheck <n> <k>  ... generates a DIMANCS CNF encoding for the specified n,k values, outputs into stdout"
        , "\tsolve <n>   ... finds the maximal k which is SAT for an nxn board"
        ]
