{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SATTypes (
    ToDimacs (..),
    ToCNF (..),
    Lit (..),
    unLit,
    isPos,
    isNeg,
    Clause (..),
    CNF (..),
    ElementaryConjunction (..),
    DNF (..),
    dimacsHeader,
    fullDimacs,
) where

import Data.List (singleton)

class ToDimacs a where
    toDimacs :: a -> String

class ToCNF t where
    toCnf :: t a -> CNF a

data Lit a
    = Pos a
    | Neg a
    deriving (Eq, Show, Functor, Foldable)
unLit :: Lit a -> a
unLit (Pos p) = p
unLit (Neg p) = p

isPos :: Lit a -> Bool
isPos (Pos _) = True
isPos _ = False

isNeg :: Lit a -> Bool
isNeg = not . isPos

newtype Clause a = Clause {clause :: [Lit a]}
    deriving (Eq, Show, Functor, Foldable, Semigroup, Monoid)

newtype CNF a = CNF {cnf :: [Clause a]}
    deriving (Eq, Show, Functor, Foldable, Semigroup, Monoid)

newtype ElementaryConjunction a = ElemConj {elemConj :: [Lit a]}
    deriving (Eq, Show, Functor, Semigroup, Monoid)

newtype DNF a = DNF {dnf :: [ElementaryConjunction a]}
    deriving (Eq, Show, Functor, Semigroup, Monoid)

instance ToDimacs (Lit Int) where
    toDimacs (Pos i) = show i
    toDimacs (Neg i) = '-' : show i

instance ToDimacs (Clause Int) where
    toDimacs = foldr (\lit acc -> toDimacs lit ++ (' ' : acc)) "0" . clause

instance ToDimacs (CNF Int) where
    toDimacs = foldr (\c acc -> toDimacs c ++ ('\n' : acc)) "" . cnf

instance ToCNF ElementaryConjunction where
    toCnf = CNF . map (Clause . singleton) . elemConj

instance ToCNF DNF where
    toCnf = CNF . map Clause . sequence . map elemConj . dnf

dimacsHeader :: Int -> Int -> String
dimacsHeader p_count clause_count = "p cnf " <> show p_count <> " " <> show clause_count

fullDimacs :: CNF Int -> String
fullDimacs cnf_expr = dimacsHeader (maximum cnf_expr) (length $ cnf cnf_expr) <> ('\n' : toDimacs cnf_expr)
