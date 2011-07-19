{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports #-}
module Language.SepPP.Parser where

import Language.SepPP.Syntax

import Unbound.LocallyNameless hiding (name,Infix,Val,Con)

import Text.Parsec hiding (ParseError,Empty)
import Text.Parsec.Error(errorMessages, messageString)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token

import Data.Typeable
import Control.Applicative hiding ((<|>),many)
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)
import Data.Char
import Text.PrettyPrint(render)

parse2 p s =
   case parse p "Input" s of
     Left d -> error(show d)
     Right e -> e

-- | Parse a string to module.
parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts = runParser sepModule () srcName cnts



-- | Lifting ParseErrors to Exceptions
deriving instance Typeable P.ParseError
instance Exception P.ParseError where

--type Parser = ParsecT String () Identity

-- | Parse an entire module
sepModule = do
  whiteSpace
  reserved "module"
  modName <- string2Name <$> identifier
  reserved "where"
  bs <- many1 sepDecl
  eof
  return $ Module modName bs




-- | Top-level binding
-- sepBinding :: Parser Binding
sepDecl = sepDataDecl <|> sepProgDecl <|> sepProofDecl <|> sepAxiomDecl

sepProgDecl = do
  (n,ty) <- sig
  (n',val) <- decl
  unless (n == n') $ do
    fail "Type signature name does not match value name"
  return $ ProgDecl n ty val
 <?> "top-level binding"
 where sig = reserved "type" >> (,) <$> exprName <* colon <*> expr <?> "top-level program type signature"
       decl = reserved "prog" >> (valDecl <|> recDecl)
       valDecl = (,) <$> exprName <* reservedOp "="  <*> expr <?> "top-level program declaration "
       recDecl = do
                reserved "rec"
                n <- exprName
                tele <- telescope <?> "rec parameters"
                reservedOp "="
                body <- expr
                return (n, Rec (bind (n,tele) body))

sepAxiomDecl = do
  reserved "axiom"
  n <- exprName
  colon
  ty <- innerExpr
  return $ AxiomDecl n ty

sepProofDecl = do
  (n,ty) <- sig
  (n',val) <- decl
  unless (n == n') $ do
    unexpected "Theorem name does not match proof name"
  return $ ProofDecl n ty val
 <?> "top-level binding"
 where sig = reserved "theorem" >> (,) <$> exprName <* colon <*> expr <?> "top-level theorem"
       decl = reserved "proof" >> (nonIndDecl <|> indDecl)
       nonIndDecl = (,) <$> exprName <* reservedOp "="  <*> expr <?>
                       "top-level proof "
       indDecl = do
          reserved "ind"
          f <- exprName
          tele <- telescope
          -- (x,ty) <- parens $ (,) <$> exprName <* colon <*> expr
          u <- braces exprName
          reservedOp "="
          body <- expr
          return $ (f,Ind (bind (f,tele,u) body))


sepDataDecl = do
  reserved "data"
  n <- name
  colon
  ps <- params
  reserved "Type"
  reserved "where"
  cs <- sepBy cons (reservedOp "|")  <?> "Constructor declaration"
  return $ DataDecl (Con n) (bind ps cs)

  where isCon (Con _) = True
        isCon _ = False
        getCons (Ann (Con a) b) = return (a,b)
        getCons _ = fail "Expecting constructor declaration"
        cons = do
                Con c <- constructor
                colon
                t <- expr
                return (c,t)
        params = option Empty $ do
                   ps <- many1 piBinding
                   reservedOp "->"
                   return $ foldr (\(st,(n,ty)) r ->
                             TCons (rebind (n,st,Embed ty) r))  Empty ps




-- Tokenizer definition
sepPPStyle = haskellStyle {
           Token.reservedNames = [
            "forall",
            "join","morejoin",
            "case", "of",
            "conv", "by", "at",
            "reserved",
            "contra", "contraabort", "using",
            "data", "where",
            "rec", "ind",
            "prog","type", "theorem", "proof", "axiom",
            "value", "values",
            "abort","aborts",
            "LogicalKind","Form", "Type","Pi",
            "ord","ordtrans",
            "let","in",
            "sym","symm","trans","refl"
           ],
           Token.reservedOpNames = ["\\", "=>", "|"]
           }


tokenizer = Token.makeTokenParser sepPPStyle
identifier = Token.identifier tokenizer
whiteSpace = Token.whiteSpace tokenizer
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer
colon = Token.colon tokenizer
semi = Token.semi tokenizer
integer = Token.integer tokenizer
brackets = Token.brackets tokenizer
parens  = Token.parens tokenizer
semiSep = Token.semiSep tokenizer
braces = Token.braces tokenizer
dot = Token.dot tokenizer
commaSep1 = Token.commaSep1 tokenizer
semiSep1 = Token.semiSep1 tokenizer
--sepBy = Token.sepBy tokenizer


alts p = do
     first <- option True (reservedOp "|">> return False)
     if first
       then sepBy1 p (reservedOp "|")
       else sepBy p (reservedOp "|")

-- name :: Rep a => Parser (Name a)
name = string2Name <$> identifier

-- exprName :: Parser EName
exprName = name


piBinding =
    (((,) Static <$> brackets binding) <?> "Static Argument Declaration") <|>
    (((,) Dynamic <$> parens binding) <?> "Dynamic Argument Declaration") <|>
    (do { v <- variable; return(Dynamic,(wildcard,v))})
  where binding = try ((,) <$> exprName <* colon <*> expr) <|>
                  (do { e <- expr; return(wildcard,e)})

nestPi [] body = body
nestPi ((stage,(n,ty)):more) body =
   Pi stage (bind (n,Embed ty) (nestPi more body))

-- "Pi(x:A)(y:x)z(List y)(q:Z) -> z x y q"
-- means  "(x : A) -> (y1 : x) -> (_2 : z) -> (_3 : List y1) -> (q4 : Z) -> z x y1 q4"
explicitPi = do
  reserved "Pi"
  bindings <- many piBinding
  reservedOp "->"
  range <- expr
  return $ nestPi bindings range
  <?> "Dependent product type with explicit 'Pi'"

piType = do
  (stage,(n,ty)) <- absBinding
  reservedOp "->"
  range <- expr
  return $ Pi stage (bind (n,Embed ty) range)
  <?> "Dependent product type"


absBinding =
    ((,) Static <$> brackets binding) <|>
    ((,) Dynamic <$> parens binding)
  where binding = (,) <$> exprName <* colon <*> expr


abstraction = unicodeAbstraction <|> asciiAbstraction
asciiAbstraction = do
  reservedOp "\\"
  args <- many absBinding
  kind <- (reservedOp "->" >> return Program)  <|>
           (reservedOp "=>" >> return Form)

  -- Formula are always static
  let g (stage,p) = if kind == Form then (Static,p) else (stage,p)
  body <- expr
  return $ nestLambda kind (map g args) body -- Lambda kind stage' (bind (n,Embed ty) body)

nestLambda kind [] body = body
nestLambda kind ((stage,(n,ty)):more) body =
   Lambda kind stage (bind (n,Embed ty) (nestLambda kind more body))

unicodeAbstraction = do
  kind <- (reservedOp "?" >> return Program) <|>
         (reservedOp "?" >> return Form)
  args <- many absBinding
  reservedOp "."
  body <- expr
  return $ nestLambda kind args body -- Lambda kind stage (bind (n,Embed ty) body)

nestForall :: [(EName, Expr)] -> Expr -> Expr
nestForall [] body = body
nestForall ((n,ty):more) body = Forall $ bind (n,Embed ty) (nestForall more body)

quantification = do
  reservedOp "?" <|> reservedOp "forall"
  pairs <- many quantBinding
  reservedOp "."
  body <- expr
  return $ nestForall pairs body -- Forall (bind (n,Embed ty) body)


quantBinding = parens $ (,) <$> exprName <* colon <*> expr


-- FIXME: The 'brackets' around termWitness are necessary because 'exprName'
-- matches 'of'. This needs to be refactored.
caseExpr = do
  reserved "case"
  scrutinee <- expr
  consEq <- braces exprName
  termWitness <- option Nothing (Just <$> expr)
  reserved "of"
  alts <- alts (alt <?> "case alternative")
  return $ Case scrutinee termWitness (bind consEq alts)
  where alt = do cons <- identifier
                 unless (isUpper (head cons)) $
                   unexpected "Pattern requires an uppercase constructor name"
                 vars <- many exprName
                 reservedOp "->"
                 body <- expr
                 return (bind (cons,vars) body)


termCase = do
  reserved "termcase"
  scrutinee <- expr
  pf <- braces exprName
  reserved "of"
  (a,t) <- do
    -- Diverges case
    ae <- do -- reservedOp "|"
             reserved "abort"
             reservedOp "->"
             expr <?> "aborts branch"

    -- Exprinates case
    te <- do reservedOp "|"
             reservedOp "!"
             reservedOp "->"
             expr <?> "terminates branch"
    return (ae,te)

  return $ TerminationCase scrutinee (bind pf (a,t))


joinExpr = do
  reserved "join"
  i0 <- integer
  i1 <- integer
  return $ Join i0 i1


morejoinExpr = do
  reserved "morejoin"
  MoreJoin <$> braces (commaSep1 innerExpr)


valExpr = reserved "value" >> Val <$> innerExpr


-- FIXME: I think the 'at' annotations are unnecessary, if we have annotations.
contraExpr = do
  reserved "contra"
  t <- innerExpr
  return $ Contra t

contraAbortExpr = do
  reserved "contraabort"
  t1 <- innerExpr
  -- reserved "using"
  t2 <- innerExpr
  return $ ContraAbort t1 t2

abortExpr = do
  reserved "abort"
  Abort <$> expr

symExpr = do
  reserved "sym" <|> reserved "symm"
  Sym <$> innerExpr

reflExpr = do
  reserved "refl"
  return $ Refl

transExpr = do
  reserved "trans"
  Trans <$> innerExpr <*> innerExpr


convExpr = do
  reserved "conv"
  a <- expr
  (convBasic a <|> convContext a)
 <?> "Conv expression"
  -- Basic-style conversion syntax, where the proofs and holes are separate.
  where convBasic a = do
             reserved "by"
             bs <- commaSep1 expr
             reserved "at"
             xs <- many1 exprName
             dot
             c <- expr
             return $ Conv a bs (bind xs c)
         -- Context-style conversion syntax
        convContext a = do
             reserved "at"
             ctx <- expr
             return $ ConvCtx a ctx


recExpr = do
  reserved "rec"
  f <- exprName
  tele <- telescope
  -- u <- brackets termName
  reservedOp "."
  body <- expr
  return $ Rec (bind (f,tele) body)
 <?> "Rec expression"


indExpr = do
  reserved "ind"
  f <- exprName
  -- (x,ty) <- parens $ (,) <$> exprName <* colon <*> expr
  tele <- telescope
  u <- braces exprName
  reservedOp "."
  body <- expr
  return $ Ind (bind (f,tele,u) body)
 <?> "Rec expression"


letdecls =
  semiSep1 (do x <- string2Name <$> identifier
               y <- brackets (string2Name <$> identifier) <?> "name for let-binding equality"
               reservedOp "="
               z <- expr
               return(x,y,z))

letExpr = do
  reserved "let"
  ds <- letdecls
  -- x <- string2Name <$> identifier
  -- y <- brackets (string2Name <$> identifier)
  -- reservedOp "="
  -- z <- expr
  reserved "in"
  body <- expr
  let letnest [] e = e
      letnest ((x,y,z):ds) e = Let (bind (x,y,Embed z) (letnest ds e))
  return $ letnest ds body -- Let (bind (x,y,Embed z) body)


escapeExpr = do
  reservedOp "~"
  Escape <$> (variable <|> parens expr)

strictExpr = do
  reserved "aborts"
  Aborts <$> innerExpr
-- Expr Productions

variable = do
  v <- varOrCon
  case v of
    Var _ -> return v
    _ -> fail "Expected variable name"

constructor = do
  c <- varOrCon
  case c of
    Con _ -> return c
    _ -> fail "Expected constructor name"


varOrCon = do
  id@(i:_) <- identifier
  if isUpper i
     then return $ Con (string2Name id)
     else return $ Var (string2Name id)

formula = reserved "Form" >> (Formula <$> option 0 integer)
sepType = reserved "Type" >> return Type

-- FIXME: Relatively certain this will cause the parser to choke.
ordExpr = reserved "ord" >> Ord <$> innerExpr
ordTrans = reserved "ordtrans" >> OrdTrans <$> innerExpr <*> innerExpr

-- FIXME: There's overlap between 'piType' and 'parens expr', hence the
-- backtracking. The 'piType' production should be moved to be a binop in expr.
innerExpr = wrapPos $
        (choice [sepType <?> "Type"
              ,formula <?> "Form"
              ,abstraction
              ,quantification
              ,caseExpr
              ,termCase
              ,explicitPi
              ,try piType
              ,joinExpr
              ,contraExpr
              ,contraAbortExpr
              ,convExpr
              ,recExpr
              ,indExpr
              ,recExpr
              ,valExpr
              ,ordExpr
              ,ordTrans
              ,letExpr
              ,escapeExpr
              ,strictExpr
                -- Derived Forms
              ,symExpr
              ,transExpr
              ,reflExpr
              ,morejoinExpr
              ,varOrCon <?> "Identifier"
              ,parens expr <?> "Parenthesized Expression"
              ] <?> "innerExpr")

factor = do
  f <- innerExpr
  args <- many arg
  return $ foldl mkApp f args
  where arg = ((,) Static <$> brackets innerExpr) <|>
              ((,) Dynamic <$> innerExpr)
        mkApp f (s,a) = App f s a

expr = wrapPos $ buildExpressionParser table factor
  where table = [[binOp AssocNone "=" Equal]
                ,[binOp AssocNone "<" IndLT]
                ,[postOp "!" Terminates]
                ,[binOp AssocLeft ":" Ann]
                ,[binOp AssocRight "->"
                          (\d r -> Pi Dynamic (bind (wildcard,Embed d) r))
                 ,binOp AssocRight "=>"
                          (\d r -> Pi Static (bind (wildcard,Embed d) r))]
                ]
        binOp assoc op f = Infix (reservedOp op >> return f) assoc
        postOp op f = Postfix (reservedOp op >> return f)
        preOp op f = Prefix (reservedOp op >> return f)


wildcard = string2Name "_"


wrapPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y


telescope = do
  ps <- many1 argBinding
  return $ teleFromList ps
 where binding stage = do
           n <- exprName
           colon
           ty <- expr
           return (stage,(n,ty))
       argBinding = parens (binding Dynamic) <|>
                    brackets (binding Static)




