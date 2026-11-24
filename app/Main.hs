{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import SATTypes (CNF (CNF), Clause (Clause), Lit (..), fullDimacs)

import Control.Arrow (Arrow ((***)), first, (&&&))
import Data.List (stripPrefix)

import Control.Monad (join)
import System.Environment (getArgs, getProgName)
import System.IO (SeekMode (AbsoluteSeek), hClose, hFlush, hGetLine, hIsEOF, hPutStr, hSeek, hSetFileSize)
import System.IO.Temp (withSystemTempFile)
import System.Process (StdStream (..), createProcess, proc, std_out, waitForProcess)

import Control.Applicative ((<|>))
import Data.Char (isSpace)
import Data.List (partition)
import Data.Maybe (isJust, mapMaybe)

data Color = White | Black
    deriving (Eq, Show, Enum, Bounded)

data Layer = LWhite | LBlack | LSum Int Color
    deriving (Eq, Show)

isLayerColor :: Layer -> Bool
isLayerColor LWhite = True
isLayerColor LBlack = True
isLayerColor _ = False

pattern LColor :: Layer
pattern LColor <- (isLayerColor -> True)

data BoardCoord l = BoardCoord
    { size :: Int
    , layer_count :: Int
    , forward_map :: l -> Int
    , backward_map :: Int -> l
    }

data GlucoseLineOutput
    = GluComment String
    | GluSAT Bool
    | GluWhitespace
    | GluModel [Lit Int]
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
        | otherwise = 1 + (forward_map bc l * (size bc) + x) * (size bc) + y
    decode bc z =
        let (lx, y) = divMod (z - 1) $ size bc
            (l, x) = divMod lx $ size bc
         in (x, y, backward_map bc l)

instance BoardEncodeDecode Layer

colToLayer :: Color -> Layer
colToLayer White = LWhite
colToLayer Black = LBlack

layerToCol :: Layer -> Color
layerToCol LWhite = White
layerToCol LBlack = Black
layerToCol _ = undefined

otherCol :: Color -> Color
otherCol White = Black
otherCol Black = White

makeBoardCoord :: Int -> Int -> BoardCoord Layer
makeBoardCoord n k =
    BoardCoord
        { size = n
        , layer_count = lc
        , forward_map = \case
            LWhite -> 0
            LBlack -> 1
            LSum x c -> 2 + k' * (fromEnum c) + x
        , backward_map = \case
            0 -> LWhite
            1 -> LBlack
            x ->
                let x' = x - 2
                    (c, x'') = first toEnum $ divMod x' k'
                 in LSum x'' c
        }
  where
    k' = k + 2 -- + 2 accounts for LSum (k + 1) and for LSum 0
    lc = 2 + 2 * (k')

encodeNxNQueen :: Int -> Int -> CNF (Int, Int, Layer)
encodeNxNQueen n k = noSameSpot <> foldl' (\acc f -> f White <> f Black <> acc) mempty [sums, kOfColor] <> allSafe
  where
    -- for all. x,y (encode x y White) != (encode x y Black) .. in truth values
    -- w = encode x y White
    -- b = encode x y White
    -- (w and not b) or (not w and b)
    -- (w or not w) and (w or b) and (not b or not w) and (not b or b)
    -- (w or b) and (not b or not w)
    noSameSpot =
        CNF
            [ Clause $ map (Neg . (x,y,)) [LWhite, LBlack]
            | x <- [0 .. (n - 1)]
            , y <- [0 .. (n - 1)]
            ]
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
    sums c =
        CNF
            [ Clause [Pos (0, 0, LSum 0 c)]
            , Clause [Neg (0, 0, LSum 1 c), Pos (0, 0, colToLayer c)] -- these two encode the case if a queen is on (0,0)
            , Clause [Pos (0, 0, LSum 1 c), Neg (0, 0, colToLayer c)] --
            ]
            <> CNF
                [ Clause [Neg (0, 0, LSum z c)] -- propagate 0,0,LSum z>=2 is false
                | z <- [2 .. k + 1]
                ]
            <> encodeNext 0 0
      where
        encodeRule1 x y prev_x prev_y =
            CNF
                [ Clause [Pos (x, y, LSum z c), Neg (prev_x, prev_y, LSum z c)]
                | z <- [0 .. k + 1]
                ]
        encodeRule2 x y prev_x prev_y =
            CNF
                [ Clause
                    [ Pos (x, y, LSum z c)
                    , Neg (prev_x, prev_y, LSum (z - 1) c)
                    , Neg (x, y, colToLayer c)
                    ]
                | z <- [1 .. k + 1]
                ]
        encodeRule3 x y prev_x prev_y =
            CNF $
                mconcat
                    [ [ Clause
                            [ prop z
                            , prev_prop z
                            , Pos (prev_x, prev_y, LSum (z - 1) c)
                            ]
                      , Clause
                            [ prop z
                            , prev_prop z
                            , Pos (x, y, colToLayer c)
                            ]
                      ]
                    | z <- [1 .. k + 1]
                    ]
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

    allSafe :: CNF (Int, Int, Layer)
    allSafe = mconcat [safe x y c | x <- [0 .. n - 1], y <- [0 .. n - 1], c <- [White, Black]]

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
    safe x y c =
        row
            <> column
            <> mconcat
                [ diag dx dy xLim yLim
                | dx <- [1, -1]
                , dy <- [1, -1]
                | xLim <- [(n - 1), 0]
                , yLim <- [(n - 1), 0]
                ]
      where
        c' = colToLayer c
        otherC = otherCol c
        otherC' = colToLayer otherC
        notA = Neg (x, y, c')

        row = CNF [Clause [notA, Neg (x', y, otherC')] | x' <- [0 .. (n - 1)], x' /= x]
        column = CNF [Clause [notA, Neg (x, y', otherC')] | y' <- [0 .. (n - 1)], y' /= y]
        diag dx dy xLim yLim =
            CNF
                [ Clause [notA, Neg (x', y', otherC')]
                | x' <- drop 1 [x, x + dx .. xLim]
                | y' <- drop 1 [y, y + dy .. yLim]
                ]

generateEncoding :: Int -> Int -> String
generateEncoding n k = fullDimacs $ fmap (\(x, y, l) -> encode bc x y l) $ encodeNxNQueen n k
  where
    bc = makeBoardCoord n k

runGlucose :: String -> a -> (String -> a -> a) -> IO a
runGlucose input initial_state reader = do
    (_, Just hStdout, _, hProcess) <- createProcess (proc "./glucose-syrup" ["-model", input]){std_out = CreatePipe}

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
    GluSAT state -> maybe (pure $ GlucoseRun state Nothing) (\s -> pure $ s{satState = state}) prev_state
    GluModel model -> maybe (pure $ GlucoseRun True (Just model)) (\s -> pure $ s{found_model = Just model}) prev_state
    GluComment _ -> prev_state
    GluWhitespace -> prev_state
  where
    parseGlucoseLine :: String -> GlucoseLineOutput
    parseGlucoseLine ('c' : xs) = GluComment $ dropWhile isSpace xs
    parseGlucoseLine ('s' : xs) = GluSAT $ isJust $ stripPrefix "SATISFIABLE" $ dropWhile isSpace xs
    parseGlucoseLine ('v' : xs) = GluModel $ parseModel $ dropWhile isSpace xs
    parseGlucoseLine _ = GluWhitespace

    parseModel = map (\p -> if p > 0 then Pos p else Neg (-p)) . takeWhile (/= 0) . map (read @Int) . words

solve :: Int -> IO (Maybe (Int, [Lit (Int, Int, Layer)]))
solve n = withSystemTempFile "encoding.cnf" $ \path h -> (fmap . fmap) (fst &&& uncurry decodeLits) $ maxK $ solvers path h
  where
    decodeLits k = map (fmap (decode $ makeBoardCoord n k))
    maxK =
        foldr
            ( \r acc ->
                r
                    >>= maybe
                        (pure Nothing)
                        ((<$> acc) . flip (<|>) . Just)
            )
            (pure Nothing)

    solvers pathEncoding hEncoding = map (solver pathEncoding hEncoding) [1 ..]
    solver pathEncoding hEncoding k = do
        putStrLn $ "trying k=" <> show k
        hSeek hEncoding AbsoluteSeek 0
        hSetFileSize hEncoding 0
        hPutStr hEncoding $ generateEncoding n k
        hFlush hEncoding

        run <- runGlucose pathEncoding Nothing parseGlucose
        pure $ case run of
            Nothing -> Nothing
            Just (GlucoseRun{satState = False}) -> Nothing
            Just (GlucoseRun{found_model = Just model}) -> Just (k, model)
            Just (GlucoseRun{found_model = Nothing}) -> error "For some reason glucose didn't return the model"

main :: IO ()
main =
    getArgs
        >>= \case
            ["check", n_str, k_str] -> do
                let (n, k) = join (***) (read @Int) (n_str, k_str)
                putStr $ generateEncoding n k
            ["solve", n_str] -> do
                let n = read @Int n_str
                solution <- solve n
                case solution of
                    Nothing -> putStrLn $ "Has no solution for n=" <> n_str
                    Just (k, model) -> do
                        let (black, white) = join (***) (map (\(x, y, _) -> (x, y))) $ partition (\case (_, _, Black) -> True; _ -> False) $ mapMaybe (\case Pos (x, y, c@LColor) -> Just (x, y, layerToCol c); _ -> Nothing) model
                        putStrLn $ "The maximal k for n=" <> n_str <> " is: " <> show k
                        putStrLn $ drawGrid n white black
            _ -> getProgName >>= putStr . usage
  where
    usage arg0 =
        unlines
            [ "USAGE: " <> arg0 <> " [COMMAND]"
            , ""
            , "COMMANDS:"
            , "\tcheck <n> <k>  ... generates a DIMANCS CNF encoding for the specified n,k values, outputs into stdout"
            , "\tsolve <n>   ... finds the maximal k which is SAT for an nxn board"
            ]

drawGrid :: Int -> [(Int, Int)] -> [(Int, Int)] -> String
drawGrid n wQueens bQueens =
    unlines
        [ [ case find (x, y) of
                Just White -> 'w'
                Just Black -> 'b'
                Nothing -> '.'
          | x <- [0 .. n - 1]
          ]
        | y <- [0 .. n - 1]
        ]
  where
    find (x, y)
        | (x, y) `elem` wQueens = Just White
        | (x, y) `elem` bQueens = Just Black
        | otherwise = Nothing
