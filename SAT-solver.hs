module SATSolver where
import Formula

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- functions atoms [True, False]]
  where atoms = atomicFormulas phi
        
        ev :: (Formula -> Bool) -> Formula -> Bool
        ev int T = True
        ev int F = False
        ev int atom@(Rel _ _) = int atom
        ev int (Not φ) = not (ev int φ)
        ev int (Or φ ψ) = ev int φ || ev int ψ
        ev int (And φ ψ) = ev int φ && ev int ψ
        ev _ φ = error $ "unexpected formula: " ++ show φ