module PropUtils where

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)
type CNFClause = [Literal]
type CNF = [CNFClause]
type PropName = String