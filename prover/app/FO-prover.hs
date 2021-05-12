{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

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
import Utils(distribute)
import SATSolver
import FOUtils

funVariants :: FunName -> [FunName]
funVariants x = x : [x ++ show n | n <- [0..]]

funsT :: Term -> FunName
funsT (Var x) = []
funsT (Fun f _) = f

fresh_consts :: [Term] -> Int -> [Term]
fresh_consts cs k =
    let l = take k [ y | y <- funVariants "fun", not $ y `elem` (map funsT cs) ]
    in map (\x -> Fun x []) l

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

prover :: FOProver
prover φ =
    let one_two = removeForall(skolemise (Not φ))
        vs = vars one_two
        consts = constants $ sig one_two
        grounds = groundInstances one_two (consts ++ fresh_consts consts 1)
    in (not . sat) (combAnd grounds)

main :: IO ()
main = do
    eof <- hIsEOF stdin
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology