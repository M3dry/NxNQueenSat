{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.List (singleton)
import Control.Monad (join)
import Control.Arrow ((***), first)

class ToDimacs a where
    toDimacs :: a -> String

class ToCNF a where
    toCnf :: a -> CNF

data Lit = Pos Int
         | Neg Int
    deriving (Eq, Show)

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

    encode bc x y l = let offset = size bc * forward_map bc l
                          x' = x + offset
                       in x' * (layer_count bc * size bc) + y
    decode bc z = let (x, y) = divMod z (layer_count bc * size bc)
                      l = backward_map bc $ x `div` (size bc)
                   in (x `mod` size bc, y `mod` size bc, l)

instance BoardEncodeDecode Layer

instance ToDimacs Lit where
    toDimacs (Pos i) = show i
    toDimacs (Neg i) = '-' : show i

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
                          LSum x c -> 2 + k*(fromEnum c) + x
    , backward_map = \case 0 -> LWhite
                           1 -> LBlack
                           x -> let x' = x - 2
                                    (c, x'') = first toEnum $ divMod x' k
                                 in LSum x'' c
    }
  where
    layer_count = 2 + k

encodeNxNQueen :: BoardCoord Layer -> Int -> CNF
encodeNxNQueen bc k = noSameSpot <> foldl' (\acc f -> f White <> f Black <> acc) mempty [sums, kOfColor]
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
    sums c = CNF [Clause [Pos $ encode bc 0 0 (LSum 0 c)]] <> encodeNext 0 0
      where
        encodeRule1 x y prev_x prev_y = CNF [ Clause [Pos $ encode bc x y (LSum z c), Neg $ encode bc prev_x prev_y (LSum z c)]
                                            | z <- [0..k+1] ]
        encodeRule2 x y prev_x prev_y = CNF [ Clause [ Pos $ encode bc x y $ LSum z c
                                                     , Neg $ encode bc prev_x prev_y $ LSum (z - 1) c
                                                     , Neg $ encode bc x y $ colToLayer c
                                                     ]
                                            | z <- [1..k+1] ]
        encodeNext x y = case advance x y of
                            Just (next_x, next_y) -> mconcat $ encodeNext next_x next_y : map (\f -> f next_x next_y x y) [encodeRule2, encodeRule1]
                            Nothing -> CNF []
        advance x y
            | y == n = Nothing -- end of the board
            | otherwise = Just (x + 1 `mod` n, if x + 1 >= n then y + 1 else y)

    -- if x,y,c, then diagonals + x row + y column all are false for the other color
    safe x y c = undefined

main :: IO ()
main = putStrLn "Hello, Haskell!"
