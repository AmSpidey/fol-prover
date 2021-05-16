module Converters where

import Formula
import FOUtils
import PropUtils
import Utils(distribute)

import qualified Data.Tuple.Extra as Tuple

-- cnf

cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go phi@(Rel _ _) = [[Pos $ show phi]]
  go (Not phi@(Rel _ _)) = [[Neg $ show phi]]
  go (φ `And` ψ) = go φ ++ go ψ
  go (φ `Or` ψ) = distribute (go φ) (go ψ)

-- ecnf

name :: Int -> PropName
name k = "MARTAVAR_" ++ show k

ecnf :: Formula -> CNF
ecnf f = concatMap cnf (Tuple.fst3 (go f 0)) where
  go :: Formula -> Int -> ([Formula], Int, Formula)
  go T 0 = ([T], 0, T)
  go F 0 = ([F], 0, F)
  go f 0 =
    let new_var = Rel (name 1) []
    in (new_var : Tuple.fst3(go f 1), 0, new_var)
  go (Not φ) k =
    let (fn, kn, pn) = go φ (k + 1)
        new_var = Rel (name k) []
    in (Iff new_var (Not pn) : fn, kn + 1, new_var)
  go (φ `And` ψ) k = go_op φ ψ AND k
  go (φ `Or` ψ) k = go_op φ ψ OR k
  go (φ `Implies` ψ) k = go_op φ ψ IMPLIES k
  go (φ `Iff` ψ) k = go_op φ ψ IFF k
  go f k = ([], k, f) where
  go_op :: Formula -> Formula -> BiOp -> Int -> ([Formula], Int, Formula)
  go_op φ ψ op k =
    let (fl, kl, pl) = go φ (k + 1)
        (fr, kr, pr) = go ψ (kl + 1)
        new_var = Rel (name k) []
    in case op of
        AND -> ([Iff new_var (pl `And` pr)] ++ fl ++ fr, kr + 1, new_var)
        OR -> ([Iff new_var (pl `Or` pr)] ++ fl ++ fr, kr + 1, new_var)
        IFF -> ([Iff new_var (pl `Iff` pr)] ++ fl ++ fr, kr + 1, new_var)
        IMPLIES -> ([Iff new_var (pl `Implies` pr)] ++ fl ++ fr, kr + 1, new_var)

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

-- skolemization for sentences

miniScoping :: Formula -> Formula
miniScoping T = T
miniScoping F = F
miniScoping rel@(Rel _ _) = rel
miniScoping f@(Forall x (And phi psi)) = if x `freeIn` phi && x `freeIn` psi then f else
    push AND FORALL x (miniScoping phi) (miniScoping psi)
miniScoping f@(Exists x (And phi psi)) = if x `freeIn` phi && x `freeIn` psi then f else
    push AND EXISTS x (miniScoping phi) (miniScoping psi)
miniScoping f@(Forall x (Or phi psi)) = if x `freeIn` phi && x `freeIn` psi then f else
    push OR FORALL x (miniScoping phi) (miniScoping psi)
miniScoping f@(Exists x (Or phi psi)) = if x `freeIn` phi && x `freeIn` psi then f else
    push OR EXISTS x (miniScoping phi) (miniScoping psi)
miniScoping (Exists x phi) = let
    phi' = miniScoping phi
    in if not (x `freeIn` phi') then phi' else Exists x phi'
miniScoping (Forall x phi) = let
    phi' = miniScoping phi
    in if not (x `freeIn` phi') then phi' else Forall x phi'
miniScoping (And phi psi) = And (miniScoping phi) (miniScoping psi)
miniScoping (Or phi psi) = Or (miniScoping phi) (miniScoping psi)
miniScoping (Not phi) = Not phi

-- pusher (Forall x (And phi psi)) = push AND FORALL x (miniScoping phi) (miniScoping psi)
-- pusher (Exists x (And phi psi)) = push AND EXISTS x (miniScoping phi) (miniScoping psi)
-- pusher (Forall x (Or phi psi)) = push OR FORALL x (miniScoping phi) (miniScoping psi)
-- pusher 
push op quant x φ ψ =
    let φ' = go quant x φ
        ψ' = go quant x ψ
    in case op of
        AND -> And φ' ψ'
        OR -> Or φ' ψ'
    where
    go quant x φ =
        if not (x `freeIn` φ) then φ
        else case quant of
            EXISTS -> Exists x φ
            _ -> Forall x φ

skolemise :: Formula -> Formula
skolemise = pnf . skolemFunc . fresh . miniScoping . nnf

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

-- generalization

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs