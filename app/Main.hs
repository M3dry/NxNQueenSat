{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main (main) where

import Data.List (singleton)
import Control.Monad (join)
import Control.Arrow ((***))

class ToDimacs a where
    toDimacs :: a -> String

class ToCNF a where
    toCnf :: a -> CNF

data Lit = Pos Int
         | Neg Int
    deriving (Eq, Show)

newtype Clause = Clause [Lit]
    deriving (Eq, Show, Semigroup, Monoid)
newtype CNF = CNF [Clause]
    deriving (Eq, Show, Semigroup, Monoid)

newtype ElementaryConjunction = ElemConj [Lit]
    deriving (Eq, Show, Semigroup, Monoid)
newtype DNF = DNF [ElementaryConjunction]
    deriving (Eq, Show, Semigroup, Monoid)

data Color = White | Black
    deriving (Eq, Show)

data BoardCoord = BoardCoord
    { encode :: Int -> Int -> Color -> Int
    , decode :: Int -> (Int, Int, Color)
    , size :: Int
    }

instance ToDimacs Lit where
    toDimacs (Pos i) = show i
    toDimacs (Neg i) = '-' : show i

instance ToDimacs Clause where
    toDimacs (Clause clause) = foldr (\lit acc -> toDimacs lit ++ (' ' : acc)) "0" clause

instance ToDimacs CNF where
    toDimacs (CNF cnf) = foldr (\clause acc -> toDimacs clause ++ ('\n' : acc)) "" cnf

instance ToCNF ElementaryConjunction where
    toCnf (ElemConj lits) = CNF $ map (Clause . singleton) lits

instance ToCNF DNF where
    toCnf (DNF []) = CNF []
    toCnf (DNF es) = CNF $ map Clause $ sequence [ls | ElemConj ls <- es]

makeBoardCoord :: Int -> BoardCoord
makeBoardCoord n = BoardCoord
    { encode = \x y c -> let offset = if c == Black then n else 0
                             (x', y') = join (***) (+ offset) (x, y)
                          in x' * (2*n) + y'
    , decode = \z -> let (x, y) = divMod z (2*n) in if x - n >= 0 then (x - n, y - n, Black) else (x, y, White)
    , size = n
    }

encodeNxNQueen :: BoardCoord -> Int -> CNF
encodeNxNQueen bc k = noSameSpot <> kOfColor White <> kOfColor Black
  where
    -- for all. x,y (encode x y White) != (encode x y Black) .. in truth values
    -- w = encode x y White
    -- b = encode x y White
    -- (w and not b) or (not w and b)
    -- (w or not w) and (w or b) and (not b or not w) and (not b or b)
    -- (w or b) and (not b or not w)
    noSameSpot = CNF [ let encoder = encode bc x y
                           w = encoder White
                           b = encoder Black
                        in Clause $ map Neg [w, b]
                     | x <- [0..(size bc - 1)], y <- [0..(size bc - 1)] ]
    -- exactly k tiles of color c are true
    -- k-clenna podmnozina [k]x[k] sjednocena na and <- DNF encoding, prevod na CNF exponencialni, mozna existuje lepsi reseni
    kOfColor c = toCnf $ DNF $ map (ElemConj . map (Pos . uncurry (flip flip c . encode bc))) $ subsets k [ (x, y) | x <- [0..(size bc - 1)], y <- [0..(size bc - 1)] ]

subsets :: Int -> [a] -> [[a]]
subsets 0 _ = [[]]
subsets _ [] = []
subsets n (x:xs) = [ x : s | s <- subsets (n - 1) xs ] ++ subsets n xs

main :: IO ()
main = putStrLn "Hello, Haskell!"
