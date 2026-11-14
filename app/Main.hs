{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}

module Main (main) where

import Data.List (singleton)
import Control.Monad (join)
import Control.Arrow ((***), first)

import System.IO (writeFile)

class ToDimacs a where
    toDimacs :: a -> String

class ToCNF a where
    toCnf :: a -> CNF

data Lit = Pos Int
         | Neg Int
    deriving (Eq, Show)
unLit :: Lit -> Int
unLit (Pos p) = p
unLit (Neg p) = p

newtype Clause = Clause [Lit]
    deriving (Eq, Show, Semigroup, Monoid)
unClause :: Clause -> [Lit]
unClause (Clause lits) = lits

newtype CNF = CNF [Clause]
    deriving (Eq, Show, Semigroup, Monoid)
unCNF :: CNF -> [Clause]
unCNF (CNF cs) = cs

newtype ElementaryConjunction = ElemConj [Lit]
    deriving (Eq, Show, Semigroup, Monoid)
unElemConj :: ElementaryConjunction -> [Lit]
unElemConj (ElemConj lits) = lits

newtype DNF = DNF [ElementaryConjunction]
    deriving (Eq, Show, Semigroup, Monoid)
unDNF :: DNF -> [ElementaryConjunction]
unDNF (DNF es) = es

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

class BoardEncodeDecode l where
    encode :: (BoardCoord l) -> Int -> Int -> l -> Int
    decode :: (BoardCoord l) -> Int -> (Int, Int, l)

    encode bc x y l
        | x < 0 || x >= size bc = error $ "Invalid x: " ++ show x
        | y < 0 || y >= size bc = error $ "Invalid y: " ++ show y
        | forward_map bc l < 0 || forward_map bc l >= size bc = error $ "Invalid y: " ++ show (forward_map bc l)
        | otherwise = (forward_map bc l * (size bc) + x) * (size bc) + y
    decode bc z = let (lx, y) = divMod z $ size bc
                      (l, x) = divMod lx $ size bc
                   in (x, y, backward_map bc l)

instance BoardEncodeDecode Layer

-- dimacs variables start from 1, but already made the encoder use 0 based so + 1 is a quick hack (hopefully won't bite me later lol)
instance ToDimacs Lit where
    toDimacs (Pos i) = show $ i + 1
    toDimacs (Neg i) = '-' : show (i + 1)

dimacsHeader :: Int -> Int -> String
dimacsHeader p_count clause_count = "p cnf " <> show p_count <> " " <> show clause_count

instance ToDimacs Clause where
    toDimacs  = foldr (\lit acc -> toDimacs lit ++ (' ' : acc)) "0" . unClause

instance ToDimacs CNF where
    toDimacs  = foldr (\clause acc -> toDimacs clause ++ ('\n' : acc)) "" . unCNF

instance ToCNF ElementaryConjunction where
    toCnf = CNF . map (Clause . singleton) . unElemConj

instance ToCNF DNF where
    toCnf = CNF . map Clause . sequence . map unElemConj . unDNF

colToLayer :: Color -> Layer
colToLayer White = LWhite
colToLayer Black = LBlack

otherCol :: Color -> Color
otherCol White = Black
otherCol Black = White

makeBoardCoord :: Int -> Int -> BoardCoord Layer
makeBoardCoord n k = BoardCoord
    { size = n
    , layer_count = layer_count
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
    layer_count = 2 + 2*(k')

encodeNxNQueen :: BoardCoord Layer -> Int -> CNF
encodeNxNQueen bc k = noSameSpot <> foldl' (\acc f -> f White <> f Black <> acc) mempty [sums, kOfColor] <> allSafe
  where
    n = size bc
    -- for all. x,y (encode x y White) != (encode x y Black) .. in truth values
    -- w = encode x y White
    -- b = encode x y White
    -- (w and not b) or (not w and b)
    -- (w or not w) and (w or b) and (not b or not w) and (not b or b)
    -- (w or b) and (not b or not w)
    noSameSpot = CNF [ Clause $ map (Neg . encode bc x y) [LWhite, LBlack]
                     | x <- [0..(n - 1)], y <- [0..(n - 1)] ]
    -- exactly k tiles of color c are true
    -- k-clenna podmnozina [k]x[k] sjednocena na and <- DNF encoding, prevod na CNF exponencialni, mozna existuje lepsi reseni
    -- kOfColor c = toCnf $ DNF $ map (ElemConj . map (Pos . uncurry (flip flip c . encode bc))) $ subsets k [ (x, y) | x <- [0..(n - 1)], y <- [0..(n - 1)] ]
    --
    -- better version using `sums`:
    -- end_x,end_y,LSum k is true and end_x,end_y,LSum K+1 is false
    kOfColor c = CNF [Clause [Pos $ encode bc (n - 1) (n - 1) $ LSum k c], Clause [Neg $ encode bc (n - 1) (n - 1) $ LSum (k + 1) c]]

    -- encodes that at x,y,(LSum z) the number of variables <x,<y,{LWhite,LBlack} is at least z
    -- x,y,(LSum z) <- (x,y)-1,(LSum z) or ((x,y)-1,(LSum z - 1) and (x,y)-1,{LWhite|LBlack})
    --    .... (x,y)-1 je predchozi policko, tj. (x-1),y iff x!= 0, jinak (n-1),y-1, base case: x,y = 0,0 plati jen pro LSum 0
    -- split into two: 1) x,y,(LSum z) <- (x,y)-1,LSum(z), and
    --                 2) x,y,(LSum z) <- ((x,y)-1,(LSum z - 1) and ((x,y)-1,LWhite or (x,y)-1,LBlack))
    --  1) w <- z = w or not z
    --  2) propagation <- (previous_prop and (white or black)) = propagation or not (previous_prop and (white or black)) =
    --     = propagation or not previous_prop or not (white or black) = propagation or (not previous_prop or (not white and not black)) =
    --     = propagation or ((not previous_prop or not white) and (not previous_prop or not black)) =
    --     = (propagation or not previous_prop or not white) and (propagation or not previous_prop or not black)
    -- also need the other diction so it's an iff, not just <-, i.e. x,y,(LSum z) -> (x,y)-1,(LSum z) or ((x,y)-1,(LSum z - 1) and (x,y)-1,{LWhite|LBlack})
    -- 3) x,y,(LSum z) -> (x,y)-1,(LSum z) = not x,y,(LSum z) or (x,y)-1,(LSum z)
    -- 4) P -> (PP and (W or B) = not P or (PP and (W or B)) = (not P or PP) and (not P or W or B)
    sums c = CNF [ Clause [Pos $ encode bc 0 0 $ LSum 0 c]
                 , Clause [Neg $ encode bc 0 0 $ LSum 1 c, Pos $ encode bc 0 0 $ colToLayer c] -- these two encode the case if a queen is on (0,0)
                 , Clause [Pos $ encode bc 0 0 $ LSum 1 c, Neg $ encode bc 0 0 $ colToLayer c] --
                 ]
          <> CNF [ Clause [Neg $ encode bc 0 0 $ LSum z c] -- propagate 0,0,LSum z>=2 is false
                 | z <- [2..k+1] ]
          <> encodeNext 0 0
      where
        encodeRule1 x y prev_x prev_y = CNF [ Clause [Pos $ encode bc x y $ LSum z c, Neg $ encode bc prev_x prev_y $ LSum z c]
                                            | z <- [0..k+1] ]
        encodeRule2 x y prev_x prev_y = CNF [ Clause [ Pos $ encode bc x y $ LSum z c
                                                     , Neg $ encode bc prev_x prev_y $ LSum (z - 1) c
                                                     , Neg $ encode bc x y $ colToLayer c
                                                     ]
                                            | z <- [1..k+1] ]
        encodeRule3 x y prev_x prev_y = CNF [ Clause [Neg $ encode bc x y $ LSum z c, Pos $ encode bc prev_x prev_y $ LSum z c]
                                            | z <- [0..k+1] ]
        encodeRule4 x y prev_x prev_y = CNF $ mconcat [ [Clause [ Neg $ encode bc x y $ LSum z c
                                                                , Pos $ encode bc prev_x prev_y $ LSum (z - 1) c
                                                                ]
                                                        , Clause [ Neg $ encode bc x y $ LSum z c
                                                                 , Pos $ encode bc x y $ colToLayer c
                                                                 ]
                                                        ]
                                                      | z <- [0..k+1] ]
        encodeNext x y = case advance x y of
                            Just (next_x, next_y) -> mconcat $ encodeNext next_x next_y : map (\f -> f next_x next_y x y) [encodeRule1, encodeRule2, encodeRule3, encodeRule4]
                            Nothing -> CNF []
        advance x y
            | x + 1 < n = Just (x + 1, y)
            | y + 1 < n = Just (0, y + 1)
            | otherwise = Nothing

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
        notA = Neg $ encode bc x y c'

        row = CNF [ Clause [notA, Neg $ encode bc x' y $ otherC'] | x' <- [0..(n - 1)], x' /= x ]
        column = CNF [ Clause [notA, Neg $ encode bc x y' $ otherC'] | y' <- [0..(n - 1)], y' /= y ]
        diag dx dy xLim yLim = CNF [ Clause [ notA, Neg $ encode bc x' y' $ otherC' ]
                                   | x' <- drop 1 [x,x+dx..xLim]
                                   | y' <- drop 1 [y,y+dy..yLim] ]

variableCount :: CNF -> Int
variableCount cnf = maximum $ map (maximum . map ((+1) . unLit) . unClause) $ unCNF cnf

fullDimacs :: CNF -> String
fullDimacs cnf = dimacsHeader (variableCount cnf) (length $ unCNF $ cnf) <> ('\n' : toDimacs cnf)

main :: IO ()
main = writeFile "encoding.cnf" $ fullDimacs $ encodeNxNQueen (makeBoardCoord 4 2) 2
