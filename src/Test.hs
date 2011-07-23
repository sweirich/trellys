{-# LANGUAGE NoMonomorphismRestriction, CPP, TypeSynonymInstances #-}
import Language.Trellys.Options
import Language.Trellys.Syntax
import Language.Trellys.Modules
import Language.Trellys.PrettyPrint
import Language.Trellys.TypeCheck
import Language.Trellys.OpSem
import Language.Trellys.Environment
import Language.Trellys.Parser
import Language.Trellys.Error
import Language.Trellys.TypeMonad
import Language.Trellys.GenericBind

import Control.Monad.Reader
import Text.PrettyPrint.HughesPJ(render)
import Text.Printf
import Control.Applicative

-- Plan
--
--   e!
--   e = (\x.b) e' -- meaning e = subst e' for x in b
--   isStrict (erase (\x.b))
--   -----------------------
--            e'!

-- TODO
--
-- - [X] parse
-- - [X] check strictness
-- - [X] check equality
-- - [ ] represent termination
--       using exists, or add a new judgement?

-- Check that argument occurs in strict position in body of erased lambda
--
-- ??? How to use where-clause with monad?
isStrict :: ETerm -> TcMonad Bool
isStrict (ELam bnd) = -- return $ body `evaluates` x
  do (x,body) <- unbind bnd
     x `isStrictIn` body
isStrict _ = return False

isStrictTerm :: Bind (Name Term) Term -> TcMonad Bool
isStrictTerm bnd = do
  (x,e) <- unbind bnd
  e'    <- erase e
  translate x `isStrictIn` e'

isStrictIn :: (Applicative m, Fresh m) => EName -> ETerm -> m Bool
x `isStrictIn` e = i e where
  -- 'i body' checks that 'x' is strict in 'body'
  i (EVar y)     = return $ x == y
  i (EApp f e)   = (||) <$> i f <*> i e
  i (ECase e _)  = i e -- could be more complete by checking that x is evaluated in all branches ...
  i (ETerminationCase e _) = i e
  i (ELet e bnd) = do (_,body) <- unbind bnd
                      (||) <$> i e <*> i body
  i _            = return False

substEq :: (Eq a, Subst b a) => a -> Name b -> b -> a -> Bool
substEq e x e' b = e == subst x e' b

-- * Examples
--   --------

s2n = string2Name

idEq = aeq (Lam Runtime
              $ bind (s2n "x")
                   $ Var (s2n "x"))
           (Lam Runtime
              $ bind (s2n "y")
                   $ Var (s2n "y"))

-- True
--
-- delPosParen removes top level position and paren info, and deep
-- version removes them all (using a generic programming function
-- called 'everywhere')
varEq1 = (delPosParen $ parse "x") `aeq` (delPosParen $ parse "x")
varEq2 = (delPosParenDeep  $ parse "x") `aeq` (delPosParenDeep  $ parse "x")
-- False: there's position info
varEq3 = parse "x" `aeq` parse "x"

conEq1 = (nakedParse "(x : Nat)") `aeq` (nakedParse "x")

-- True
lamEq1 = (Lam Runtime $ bind (s2n "x") (nakedParse "x"))
   `aeq` (Lam Runtime $ bind (s2n "y") (nakedParse "y"))

-- * Tests
--   -----

-- ??? without this instance nothing happens when I evaluate test in GHC ??? (or anything in IO (Either Err t))
--
-- where test was runTcMonad' (isStrict EJoin)
instance Show Err where
  show = render . disp

runTcMonad' = runTcMonad (emptyEnv [])
r = runTcMonad'

right (Right e) = e

parseVar = testParser variable

parse :: String -> Term
parse = right . parseExpr
nakedParse :: String -> Term
nakedParse = delPosParenDeep . parse
parseAndErase :: String -> TcMonad ETerm
parseAndErase = erase . nakedParse
parseAndIsStrict = runTcMonad' . (isStrict =<<) . erase . nakedParse

--testIsStrict :: String -> String -> TcMonad Bool
testIsStrict sx se = do
  let x = right $ parseVar sx
      e = nakedParse se
      c = bind x e
  r <- right <$> (runTcMonad' $ isStrictTerm c)
  printf "%6s : %s . %s\n" (show r) sx se

sx `isStrictIn'` se = do
  let x = s2n sx
--  e <- right <$> parseAndErase se
  e <- erase $ nakedParse se
  return e
--  return $ x `isStrictIn` e

testSubst se se' sx sc =
  let e  = nakedParse se
      e' = nakedParse se'
      x  = right $ parseVar sx
      c  = nakedParse sc
  in e `aeq` subst x e' c

test = testIsStrict
test' se se' sx sc = do
  let b = testSubst se se' sx sc
  printf "%6s : (%s) (%s) %s . %s\n" (show b) se se' sx sc

main = do
  putStrLn "Strictness Tests"
  putStrLn "================"

  putStrLn "Should be True:"
  test "x" "x"
  test "x" "\\[y] . x"
  test "x" "case x [_] of {}"
  test "x" "let y [_] = z in x"
  test "x" "let y [_] = x in y"
  test "x" "let y [_] = x in z"
  test "x" "x y"
  test "x" "y x"
  test "x" "C x"
  test "x" "y (y x)"
  test "x" "(y (y x)) y"
  test "x" "case (x [y]) [_] of {}"
  test "x" "let x [_] = x in x"

  putStrLn "Should be False:"
  test "x" "y"
  test "x" "\\y . x"
  -- this case is actually True, but we don't handle it (x strict in
  -- all branches)
  test "x" "case y [_] of {C -> x}"
  test "x" "let x [_] = y in x"
  test "x" "y [x]"
  test "x" "case (y [x]) [_] of {}"

  putStrLn "Substitution Tests"
  putStrLn "=================="

  test' "S Z" "Z" "x" "S x"
  test' "case (S (S Z)) [_] of {C -> D}" "S (S Z)" "x" "case x [_] of {C -> D}"
  test' "f (f x)" "x" "y" "f y"
  -- the equality is substition equality, not joinability of erased
  -- terms, so the following fails
  test' "\\[y] . x" "x" "y" "y"
  test' "\\[y] . x" "x" "y" "\\[z] . y"
