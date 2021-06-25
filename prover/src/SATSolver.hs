module SATSolver where

import Formula
import Utils (functions, distribute, remSuperList)
import FOUtils (atomicFormulas)
import PropUtils
import Converters(ecnf)
import qualified Data.HashSet as HS hiding (map)
import Data.Hashable
import Data.List
import Data.Function
import qualified Data.Tuple.Extra as Tuple

instance Hashable Literal where
  hashWithSalt s (Pos p) = hashWithSalt s (hashWithSalt s p)
  hashWithSalt s (Neg p) = hashWithSalt s (-(hashWithSalt s p))

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

positiveLiterals :: CNFClause -> [PropName]
positiveLiterals ls = nub [p | Pos p <- ls]

negativeLiterals :: CNFClause -> [PropName]
negativeLiterals ls = nub [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nub $ positiveLiterals ls ++ negativeLiterals ls

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

remTautos :: CNF -> CNF
remTautos [] = []
remTautos [[]] = [[]]
remTautos cnf = filter go cnf where
    go clause =
        let pl = positiveLiterals clause
            nl = negativeLiterals clause
            intersection = intersect pl nl
        in case intersection of
            [] -> True
            _ -> False

oneLiterals :: CNF -> HS.HashSet Literal
oneLiterals [] = HS.empty
oneLiterals ([Pos p]:tl) = HS.insert (Pos p) (oneLiterals tl)
oneLiterals ([Neg p]:tl) = HS.insert (Neg p) (oneLiterals tl)
oneLiterals (h:tl) = oneLiterals tl

oneLiteral :: CNF -> CNF
oneLiteral [] = []
oneLiteral [[]] = [[]]
oneLiteral cnf =
    let literals = oneLiterals cnf
        non_absurd = foldr (\a b -> not (HS.member (opposite a) literals) && b) True literals
    in case non_absurd of
        False -> [[]]
        True -> go literals cnf where
            go :: HS.HashSet Literal -> CNF -> CNF
            go h [] = []
            go h ([Pos p]:t) = go h t
            go h ([Neg p]:t) = go h t
            go h (clause:t) = if foldr (\l b -> not (HS.member l literals) && b) True clause then (
                                  let filtered = [filter (\l -> not $ HS.member (opposite l) literals) clause]
                                  in case filtered of
                                      [[]] -> [[]]
                                      _ -> filtered ++ go h t) else go h t

affirmNeg :: CNF -> CNF
affirmNeg cnf = let
    pl = HS.fromList $ concatMap positiveLiterals cnf
    nl = HS.fromList $ concatMap negativeLiterals cnf
    to_remove = HS.union (HS.difference pl nl) (HS.difference nl pl)
    in filter (foldr (\l b -> not (HS.member (literal2var l) to_remove) && b ) True) cnf

leastCommonVar :: CNF -> PropName
leastCommonVar cnf = go $ positiveLiterals con_cnf ++ negativeLiterals con_cnf where
      go :: [PropName] -> PropName
      go = head . minimumBy (compare `on` length) . group . sort

      con_cnf = concat cnf

resolution :: CNF -> CNF
resolution [] = []
resolution [[]] = [[]]
resolution cnf = go (leastCommonVar cnf) cnf where
    go :: PropName -> CNF -> CNF
    go l cnf =
      let pos_rest = partition (elem $ Pos l) cnf
          neg_rest = partition (elem $ Neg l) (snd pos_rest)
          positives = map (filter (/= Pos l)) (fst pos_rest)
          negatives = map (filter (/= Neg l)) (fst neg_rest)
      in nub $ remSuperList $ distribute positives negatives ++ snd neg_rest

doWhileCan :: (CNF -> CNF) -> CNF -> CNF -> CNF
doWhileCan f x y = if x == y then x else doWhileCan f y (f y)

dpSatSolver :: SATSolver
dpSatSolver = solve . ecnf where
    solve :: CNF -> Bool
    solve [] = True
    solve [[]] = False
    solve cnf = solve (resolution $ doWhileCan go (cnf ++ [[]]) cnf) where
        go :: CNF -> CNF
        go cnf =
          let rt = remTautos cnf
              ol = doWhileCan oneLiteral (rt ++ [[]]) rt
              an = doWhileCan affirmNeg (ol ++ [[]]) ol
          in an