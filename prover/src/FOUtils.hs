module FOUtils where

import Control.Monad.State
import Data.List
import qualified Data.HashMap.Strict as HM hiding (map)
import Data.Hashable

import Formula
import Utils(distribute, replaceComb)

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

-- enumerate variants of a variable name

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ ts) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

-- fresh rename

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = not $ x `elem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, not $ y `elem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

hasQuants (Exists _ φ) = True
hasQuants (Forall _ φ) = True
hasQuants φ = False

-- ground instances

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances f ts = let
    combs = replaceComb (vars f) ts
    frees = fv f
    in if null combs || null frees then [f] else map (groundRepl f . HM.fromList) combs
groundRepl :: Formula -> HM.HashMap VarName Term -> Formula
groundRepl f hm = apply (hm HM.!) f

