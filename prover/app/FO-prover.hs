{-# LANGUAGE UnicodeSyntax, FlexibleInstances, ParallelListComp, FlexibleContexts #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)
import Utils(combWithRep)
import SATSolver
import FOUtils
import Converters


funVariants :: FunName -> [FunName]
funVariants x = x : [x ++ show n | n <- [0..]]

funsT :: Term -> FunName
funsT (Var x) = []
funsT (Fun f _) = f

fresh_consts :: [Term] -> Int -> [Term]
fresh_consts cs k =
    let l = take k [ y | y <- funVariants "fun", notElem y (map funsT cs) ]
    in map (`Fun` []) l

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = [Fun c [] | (c, 0) <- s]

combAnd :: [Formula] -> Formula
combAnd [] = F
combAnd [f] = f
combAnd (f:fs) = And f (combAnd fs)

removeForall :: Formula -> Formula
removeForall (Forall _ φ) = removeForall φ
removeForall φ = φ

kUniverse :: Signature -> Int -> [Term]
kUniverse sig 0 =
    let consts = constants sig
        consts' = if null consts then fresh_consts consts 1 else consts
    in consts'
kUniverse sig k = [Fun f vrs | (f, ar) <- sig, vrs <- combWithRep ar (kUniverse sig (k - 1))]

prover :: FOProver
prover φ =
    let one_two = removeForall(skolemise $ generalise (Not φ))
        signature = sig one_two
    in loop 0 signature one_two
    where
        loop 0 sig ψ =
            let res = (not . and) [dpSatSolver $ combAnd $ groundInstances ψ $ kUniverse sig 0]
            in if length (constants sig) == length sig || res then res
            else loop 1 sig ψ
        loop n sig ψ
            | (not . and) [dpSatSolver $ combAnd $ groundInstances ψ $ concat [kUniverse sig k | k <- [1..n]]] = True
            | otherwise = loop (n + 1) sig ψ
main :: IO ()
main = do
    eof <- isEOF
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology