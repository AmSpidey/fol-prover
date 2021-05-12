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

combAnd :: [Formula] -> Formula
combAnd [] = F
combAnd [f] = f
combAnd (f:fs) = And f (combAnd fs)

removeForall :: Formula -> Formula
removeForall (Forall _ φ) = removeForall φ
removeForall φ = φ

prover :: FOProver
prover =
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