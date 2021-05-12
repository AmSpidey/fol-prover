module FOUtils where

import Control.Monad.State
import Data.List
import qualified Data.HashMap.Strict as HM hiding (map)
import Data.Hashable

import Formula
import Utils(distribute)


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

-- generalization

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

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

-- negation normal form
nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Rel f t) = Rel f t
nnf (Not (Rel f t)) = Not (Rel f t)
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf $ Not phi) (nnf psi)
nnf (Iff phi psi) = And (nnf $ Implies phi psi) (nnf $ Implies psi phi)
nnf (Exists var phi) = Exists var (nnf phi)
nnf (Forall var phi) = Forall var (nnf phi)
nnf (Not T) = F
nnf (Not F) = T
nnf (Not (And phi psi)) = Or (nnf $ Not phi) (nnf $ Not psi)
nnf (Not (Or phi psi)) = And (nnf $ Not phi) (nnf $ Not psi)
nnf (Not (Implies phi psi)) = And (nnf phi) (nnf $ Not psi)
nnf (Not (Iff phi psi)) = Or (nnf $ Not $ Implies phi psi) (nnf $ Not $ Implies psi phi)
nnf (Not (Not phi)) = nnf phi
nnf (Not (Forall var phi)) = Exists var (nnf (Not phi))
nnf (Not (Exists var phi)) = Forall var (nnf (Not phi))

-- prenex normal form
data Quantifier
  = EXISTS
  | FORALL

data BiOp
  = AND
  | OR
  | IMPLIES
  | IFF

hasQuants (Exists _ φ) = True
hasQuants (Forall _ φ) = True
hasQuants φ = False

form op quant var φ ψ =
    let inside = case op of
          AND -> And φ ψ
          OR -> Or φ ψ
    in case quant of
        EXISTS -> Exists var inside
        FORALL -> Forall var inside

pull op quant var φ ψ = if freshIn var ψ then form op quant var φ ψ else
  (let new_var = freshVariant var (form op quant var φ ψ) in form op quant new_var (rename var new_var φ) ψ)

pnf :: Formula -> Formula
pnf = go . nnf where
    go :: Formula -> Formula
    go T = T
    go F = F
    go (Not f) = Not f
    go (Rel r t) = Rel r t
    go (Exists x φ) = Exists x (go φ)
    go (Forall x φ) = Forall x (go φ)
    go (And (Exists x φ) ψ) = go $ pull AND EXISTS x (go φ) (go ψ)
    go (And (Forall x φ) ψ) = go $ pull AND FORALL x (go φ) (go ψ)
    go (And ψ (Exists x φ)) = go (And (Exists x φ) ψ)
    go (And ψ (Forall x φ)) = go (And (Forall x φ) ψ)
    go (Or (Exists x φ) ψ) = go $ pull OR EXISTS x (go φ) (go ψ)
    go (Or (Forall x φ) ψ) = go $ pull OR FORALL x (go φ) (go ψ)
    go (Or ψ (Exists x φ)) = go (Or (Exists x φ) ψ)
    go (Or ψ (Forall x φ)) = go (Or (Forall x φ) ψ)
    go (And φ ψ) = let
        fip = go φ
        phip = go ψ
        in if hasQuants fip || hasQuants phip then go (And fip phip) else And fip phip
    go (Or φ ψ) = let
        fip = go φ
        phip = go ψ
        in if hasQuants fip || hasQuants phip then go (Or fip phip) else Or fip phip

-- skolemization

skolemise :: Formula -> Formula
skolemise = pnf . skolemFunc . fresh . nnf . generalise

skolemFunc :: Formula -> Formula
skolemFunc = go [] where
    go :: [Term] -> Formula -> Formula
    go vars (Forall x phi) = Forall x (go (vars ++ [Var x]) phi)
    go vars (Exists y phi) = apply (\k -> if k == y then Fun y vars else Var k) (go vars phi)
    go vars T = T
    go vars F = F
    go vars (Not phi) = Not (go vars phi)
    go vars (And phi psi) = And (go vars phi) (go vars psi)
    go vars (Or phi psi) = Or (go vars phi) (go vars psi)
    go vars (Implies phi psi) = Implies (go vars phi) (go vars psi)
    go vars (Iff phi psi) = Iff (go vars phi) (go vars psi)
    go vars (Rel r ts) = Rel r ts

-- ground instances

combWithRep :: Int -> [a] -> [[a]]
combWithRep 0 l = []
combWithRep 1 l = [[x] | x <- l]
combWithRep k l = distribute (combWithRep (k - 1) l) [[x] | x <- l]

replaceComb :: [a] -> [b] -> [[(a, b)]]
replaceComb vars ts = [zip vars z | z <- combWithRep (length vars) ts]

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances f ts = map (go f . HM.fromList) (replaceComb (vars f) ts) where
    go :: Formula -> HM.HashMap VarName Term -> Formula
    go f hm = apply (hm HM.!) f

