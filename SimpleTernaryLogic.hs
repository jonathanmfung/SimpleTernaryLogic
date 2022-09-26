{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

import Prelude hiding
  ( (>>),
    (||),
  )

data Syst
  = Kleene
  | Lukasiewicz
  | Bochvar

data Expression
  = F
  | U
  | T
  | Not Expression -- not
  | And Expression Expression -- and
  | Or Expression Expression -- or
  | Implies Expression Expression -- impl
  | Bicond Expression Expression -- equivalence
  deriving (Eq)

instance Show Expression where
  show (Not a) = "¬" ++ show a
  show (And a b) = "(" ++ show a ++ " ∧ " ++ show b ++ ")"
  show (Or a b) = "(" ++ show a ++ " ∨ " ++ show b ++ ")"
  show (Implies a b) = "(" ++ show a ++ " → " ++ show b ++ ")"
  show (Bicond a b) = "(" ++ show a ++ " ↔ " ++ show b ++ ")"
  show F = "F"
  show U = "U"
  show T = "T"

-- (\e1 e2 -> ((e2 || e1) >> ((!) e2) <-> e1)) T F

type Op = Expression -> Expression -> Expression

(!) = Not

(&), (||), (>>), (<->) :: Op
a & b = And a b
a || b = Or a b
a >> b = Implies a b
a <-> b = Bicond a b

evaluate :: Syst -> Expression -> Expression
evaluate Kleene exps = eval exps
  where
    -- https://en.wikipedia.org/wiki/Three-valued_logic#Kleene_and_Priest_logics

    eval :: Expression -> Expression
    eval (Implies a b) = eval (Or (eval $ Not a) (eval b))
    eval (And F _) = F
    eval (And _ F) = F
    eval (And U _) = U
    eval (And _ U) = U
    eval (And T T) = T
    eval (And e1 e2) = eval $ And (eval e1) (eval e2)
    eval (Or T _) = T
    eval (Or _ T) = T
    eval (Or U _) = U
    eval (Or _ U) = U
    eval (Or F F) = F
    eval (Or e1 e2) = eval $ Or (eval e1) (eval e2)
    eval (Bicond U _) = U
    eval (Bicond _ U) = U
    eval (Bicond T T) = T
    eval (Bicond F F) = T
    eval (Bicond F T) = F
    eval (Bicond T F) = F
    eval (Bicond e1 e2) = eval $ Bicond (eval e1) (eval e2)
    eval (Not F) = T
    eval (Not U) = U
    eval (Not T) = F
    eval (Not e) = eval $ Not $ eval e
    eval e = e
evaluate Lukasiewicz exps = eval exps
  where
    -- https://en.wikipedia.org/wiki/Three-valued_logic#%C5%81ukasiewicz_logic

    eval :: Expression -> Expression
    eval (Implies F _) = T
    eval (Implies _ T) = T
    eval (Implies U U) = T
    eval (Implies T U) = U
    eval (Implies U F) = U
    eval (Implies T F) = F
    eval (Implies e1 e2) = eval $ Implies (eval e1) (eval e2)
    eval (Or a b) =
      eval $
        Implies
          (eval $ Implies (eval a) (eval b))
          (eval b)
    eval (And a b) =
      eval $
        Not
          (Or (Not (eval a)) (Not (eval b)))
    eval (Bicond a b) =
      eval $
        And
          (Implies (eval a) (eval b))
          (Implies (eval b) (eval a))
    eval (Not F) = T
    eval (Not U) = U
    eval (Not T) = F
    eval (Not e) = eval $ Not $ eval e
    eval e = e
evaluate Bochvar exps = eval exps
  where
    -- https://en.wikipedia.org/wiki/Many-valued_logic#Bochvar's_internal_three-valued_logic

    eval :: Expression -> Expression
    eval (Implies U _) = U
    eval (Implies _ U) = U
    eval (Implies F _) = T
    eval (Implies T F) = F
    eval (Implies T T) = T
    eval (Implies e1 e2) = eval $ Implies (eval e1) (eval e2)
    eval (And U _) = U
    eval (And _ U) = U
    eval (And F _) = F
    eval (And _ F) = F
    eval (And T T) = T
    eval (And e1 e2) = eval $ And (eval e1) (eval e2)
    eval (Or U _) = U
    eval (Or _ U) = U
    eval (Or T _) = T
    eval (Or _ T) = T
    eval (Or F F) = F
    eval (Or e1 e2) = eval $ Or (eval e1) (eval e2)
    eval (Bicond U _) = U
    eval (Bicond _ U) = U
    eval (Bicond T T) = T
    eval (Bicond F F) = T
    eval (Bicond F T) = F
    eval (Bicond T F) = F
    eval (Bicond e1 e2) = eval $ Bicond (eval e1) (eval e2)
    eval (Not F) = T
    eval (Not U) = U
    eval (Not T) = F
    eval (Not e) = eval $ Not $ eval e
    eval e = e

data Row a = Row
  { fCol :: a,
    uCol :: a,
    tCol :: a
  }
  deriving (Functor)

instance (Show a) => Show (Row a) where
  show (Row f u c) = show f ++ "\t" ++ show u ++ "\t" ++ show c

data Table a = Table
  { fRow :: Row a,
    uRow :: Row a,
    tRow :: Row a
  }
  deriving (Functor)

instance (Show a) => Show (Table a) where
  show (Table f u c) =
    "\tF.\tU.\tT.\n"
      ++ "F:\t"
      ++ show f
      ++ "\n"
      ++ "U:\t"
      ++ show u
      ++ "\n"
      ++ "T:\t"
      ++ show c

baseTTable =
  Table
    { fRow = Row (F, F) (F, U) (F, T),
      uRow = Row (U, F) (U, U) (U, T),
      tRow = Row (T, F) (T, U) (T, T)
    }

truthTable :: Syst -> Op -> Table Expression
truthTable sys op = evalPairs <$> baseTTable
  where
    evalPairs = evaluate sys . uncurry op

-- Table is for showing how an Op works
-- Op is usually basic And/Or
-- Op can also be some general expression that reduces input table ot final result
-- ex: andOr
-- ex: truthTable Lukasiewicz (\e1 e2 -> ((e2 || e1) >> (e2) <-> e1))

andOr :: Op
andOr = \e1 e2 -> (e1 & e2) || e2

-------------------------------------------------------
-- Extra code

--   F U T
-- F
-- U
-- T
testTable :: Syst -> (Expression -> Expression -> Expression) -> [[Expression]] -- Op
testTable sys op = rows
  where
    list :: [[(Expression, Expression)]]
    list = [[(x, y) | y <- [F, U, T]] | x <- [F, U, T]]
    rows :: [[Expression]]
    rows = [map (evaluate sys . uncurry op) r | r <- list]

tests =
  and
    [ testTable Kleene And == [[F, F, F], [F, U, U], [F, U, T]],
      testTable Kleene Or == [[F, U, T], [U, U, T], [T, T, T]],
      testTable Kleene Implies == [[T, T, T], [U, U, T], [F, U, T]],
      testTable Kleene Bicond == [[T, U, F], [U, U, U], [F, U, T]],
      testTable Lukasiewicz Implies == [[T, T, T], [U, T, T], [F, U, T]]
    ]

-- either print a contingency table or just all combinations in line
--   a b
-- c T F
-- d T F
--
-- x y res
-- a c T
-- b c F
-- a d T
-- b d F

transpose :: [[a]] -> [[a]]
transpose ([] : _) = []
transpose x = map head x : transpose (map tail x)

-- transpose [[1,2,3],[4,5,6],[7,8,9]]

test'' :: [[Expression]]
test'' = transpose [alpha, beta, res]
  where
    pairs = [(x, y) | x <- [F, U, T], y <- [F, U, T]]
    alpha = map fst pairs
    beta = map snd pairs
    res = map (evaluate Kleene . uncurry And) pairs

testPrint :: [[Expression]] -> IO ()
testPrint rows =
  putStrLn $
    concatMap
      ( (++ "\n")
          . concatMap ((++) " " . show)
      )
      rows

parseArg :: String -> Maybe Syst
parseArg s = case s of
  "Kleene" -> Just Kleene
  "Lukasiewicz" -> Just Lukasiewicz
  _ -> Nothing
