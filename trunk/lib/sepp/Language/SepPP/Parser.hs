{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp #-}
module Language.SepPP.Parser where

import Language.SepPP.Syntax
import Language.SepPP.Options

import Unbound.LocallyNameless hiding (name,Infix,Val,Con,Equal,Refl)

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
import qualified Data.IntMap as IM

parse2 p s =
   case parse p "Input" s of
     Left d -> error(show d)
     Right e -> e

-- | Parse a string to module.
parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts = runParser sepModule initialParserState srcName cnts

-- User state, so that we can update the operator parsing table.
data ExprParserState =
  ExprParserState {
    exprParser :: Parsec String ExprParserState Expr,
    exprOpTable :: IM.IntMap [Operator String ExprParserState Identity Expr]
    }

initialParserState = ExprParserState {
  exprParser = buildExpressionParser initialTable factor,
  exprOpTable = IM.fromAscList (zip [0..] initialTable)
  }



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
sepDecl = sepDataDecl <|> sepProgDecl <|> sepProofDecl <|> sepAxiomDecl <|>
          sepTheoremDecl <|> sepProgramDecl <|>
          sepInductiveDecl <|> sepRecursiveDecl <|>
          sepFlag <|> sepOperator

sepProgDecl = do
  (n,ty) <- sig
  (n',val) <- decl
  unless (n == n') $ do
    fail "Type signature name does not match value name"
  return $ ProgDecl n ty val
 <?> "top-level binding"
 where sig = reserved "type" >> (,) <$> varName <* colon <*> expr <?> "top-level program type signature"
       decl = reserved "prog" >> (valDecl <|> recDecl)
       valDecl = (,) <$> varName <* reservedOp "="  <*> expr <?> "top-level program declaration "
       recDecl = do
                reserved "rec"
                n <- varName
                tele <- telescope <?> "rec parameters"
                reservedOp "="
                body <- expr
                return (n, Rec (bind (n,tele) body))

sepAxiomDecl = do
  reserved "axiom"
  n <- varName
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
 where sig = reserved "theorem" >> (,) <$> varName <* colon <*> expr <?> "top-level theorem"
       decl = reserved "proof" >> (nonIndDecl <|> indDecl)
       nonIndDecl = (,) <$> varName <* reservedOp "="  <*> expr <?>
                       "top-level proof "
       indDecl = do
          reserved "ind"
          f <- varName
          tele <- telescope
          -- (x,ty) <- parens $ (,) <$> varName <* colon <*> expr
          u <- braces varName
          reservedOp "="
          body <- expr
          return $ (f,Ind (bind (f,tele,u) body))


sepTheoremDecl = do
  reserved "Theorem"
  n <- varName
  colon
  reserved "forall"
  qvars <- many1 piBinding
  reservedOp "."
  ran <- expr
  reservedOp ":="
  body <- expr
  let ty = foldr (\(_,(inf,n,ty)) rest -> Forall (bind (n,Embed ty,inf) rest)) ran qvars
      term = foldr (\(_,(_,n,ty)) rest -> Lambda Form Static (bind (n,Embed ty) rest)) body qvars
  return $ ProofDecl n ty term

sepProgramDecl = do
  reserved "Program"
  n <- varOrOpName
  colon
  qvars <- option [] $ try $ do
    qvars <- many1 piBinding
    reservedOp "->"
    return qvars
  ran <- expr
  reservedOp ":="
  body <- expr
  let ty = foldr (\(stage,(inf,n,ty)) rest -> Pi stage (bind (n,Embed ty,inf) rest)) ran qvars
      term = foldr (\(stage,(_,n,ty)) rest -> Lambda Program stage (bind (n,Embed ty) rest)) body qvars
  return $ ProgDecl n ty term
  where varOrOpName = varName <|> parens (string2Name <$> operator)

sepRecursiveDecl = do
  reserved "Recursive"
  n <- varOrOpName
  colon
  tele <- telescope
  reservedOp "->"
  ran <- expr
  reservedOp ":="
  body <- expr
  let ty = fTele (\(n,stage,ty,inf) rest -> Pi stage (bind (n,ty,inf) rest)) ran tele
      term = Rec (bind (n,tele) body)
  return $ ProgDecl n ty term
  where varOrOpName = varName <|> parens (string2Name <$> operator)

sepInductiveDecl = do
  reserved "Inductive"
  n <- varName
  colon
  reserved "forall"
  tele1 <- telescope <?> "tele1"
  iv <- braces varName <?> "inductive size proof"
  tele2 <- option Empty telescope
  reservedOp "."
  ran <- expr
  reservedOp ":="
  body <- expr
  (ind,_,_,_) <- lastTele tele1
  let ty2 = fTele (\(n,stage,ty,inf) rest -> Forall (bind (n,ty,inf) rest)) ran tele2

      ty3 = Forall (bind (iv,Embed (Terminates (Var ind)),False) ty2)
      ty1 = fTele (\(n,stage,ty,inf) rest -> Forall (bind (n,ty,inf) rest)) ty3 tele1
      terms2 = fTele (\(n,_,ty,inf) rest -> Lambda Form Static (bind (n,ty) rest)) body tele2
      -- terms3 = Lambda Form Static (bind (n,Terminates (Var ind)) terms2)
      -- terms1 = fTele (\(n,_,ty,inf) rest -> Lambda Form Static (bind (n,ty) rest)) terms3 tele2
  return $ ProofDecl n ty1 (Ind (bind (n,tele1,iv) terms2))

  where lastTele (TCons rebinding) =
          case unrebind rebinding of
            (pat,Empty) -> return pat
            (_,t@(TCons _)) -> lastTele t
        lastTele Empty = unexpected "Argument list for inductive definition must be non-empty"


sepDataDecl = do
  reserved "data"
  n <- consName
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
                   return $ foldr (\(st,(inf,n,ty)) r ->
                             TCons (rebind (n,st,Embed ty,inf) r))  Empty ps




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
            "value", "values","valax",
            "show",
            "abort","aborts",
            "LogicalKind","Form", "Type","Pi",
            "ord","ordtrans",
            "let","in",
            "sym","symm","trans","refl", "tcast",
            "set", -- for flags
            "Theorem", "Program", "Inductive", "Recursive",
            "infix", "infixl", "infixr", "pre", "post",
            "exists","as","pack","unpack"
           ],
           Token.reservedOpNames = ["\\", "=>", "|","?",".",":="]
           }


tokenizer = Token.makeTokenParser sepPPStyle
identifier = Token.identifier tokenizer
whiteSpace = Token.whiteSpace tokenizer
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer
operator = Token.operator tokenizer
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
comma = Token.comma tokenizer


alts p = do
     first <- option True (reservedOp "|">> return False)
     if first
       then sepBy1 p (reservedOp "|")
       else sepBy p (reservedOp "|")

-- name :: Rep a => Parser (Name a)
-- name = string2Name <$> identifier

-- varName :: Parser EName
varName = do
  n <- identifier
  when (null n || isUpper (head n)) $
       unexpected "Variable names must begin with a lowercase letter"
  return (string2Name n)
consName = do
  n <- identifier
  when (null n || isLower (head n)) $
       unexpected "Constructor names must begin with an uppercase letter"
  return (string2Name n)


piBinding =
    (((,) Static <$> (try $ brackets binding)) <?> "Static Argument Declaration") <|>
    (((,) Dynamic <$> (try $ parens binding)) <?> "Dynamic Argument Declaration") <|>
    (do { v <- variable; return(Dynamic,(False,wildcard,v))})
  where binding = try ((,,) <$> infOption <*> varName <* colon <*> expr) <|>
                  (do { e <- expr; return(False,wildcard,e)})

nestPi [] body = body
nestPi ((stage,(inf,n,ty)):more) body =
   Pi stage (bind (n,Embed ty,inf) (nestPi more body))

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
  (stage,(inf,n,ty)) <- absBinding
  reservedOp "->"
  range <- expr
  return $ Pi stage (bind (n,Embed ty,inf) range)
  <?> "Dependent product type"


absBinding =
    ((,) Static <$> brackets binding) <|>
    ((,) Dynamic <$> parens binding)
  where binding = (,,) <$> infOption <*> varName <* colon <*> expr


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
nestLambda kind ((stage,(_,n,ty)):more) body =
   Lambda kind stage (bind (n,Embed ty) (nestLambda kind more body))

unicodeAbstraction = do
  kind <- (reservedOp "?" >> return Program) <|>
         (reservedOp "?" >> return Form)
  args <- many absBinding
  reservedOp "."
  body <- expr
  return $ nestLambda kind args body -- Lambda kind stage (bind (n,Embed ty) body)

nestForall :: [(Bool, EName, Expr)] -> Expr -> Expr
nestForall [] body = body
nestForall ((inf,n,ty):more) body = Forall $ bind (n,Embed ty,inf) (nestForall more body)

quantification = do
  reservedOp "?" <|> reservedOp "forall"
  pairs <- many quantBinding
  reservedOp "."
  body <- expr
  return $ nestForall pairs body -- Forall (bind (n,Embed ty) body)


quantBinding = parens $ (,,) <$> infOption <*> varName <* colon <*> expr

-- FIXME: The 'brackets' around termWitness are necessary because 'varName'
-- matches 'of'. This needs to be refactored.
caseExpr = do
  reserved "case"
  scrutinee <- expr
  consEq <- braces varName
  termWitness <- option Nothing (Just <$> expr)
  reserved "of"
  alts <- alts (alt <?> "case alternative")
  return $ Case scrutinee termWitness (bind consEq alts)
  where alt = do cons <- identifier
                 unless (isUpper (head cons)) $
                   unexpected "Pattern requires an uppercase constructor name"
                 vars <- many varName
                 reservedOp "->"
                 body <- expr
                 return (bind (cons,vars) body)


termCase = do
  reserved "termcase"
  scrutinee <- expr
  pf <- braces varName
  reserved "of"
  (a,t) <- do
    -- Diverges case
    ae <- do -- reservedOp "|"
             reserved "abort"
             reservedOp "->"
             expr <?> "aborts branch"

    -- Terminates case
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


valExpr = (reserved "value" <|> reserved "valax") >> Val <$> innerExpr


tcastExpr = reserved "tcast" >>TCast <$> innerExpr <* reserved "by" <*> innerExpr


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

showExpr = do
  reserved "show"
  Show <$> expr

symExpr = do
  reserved "sym" <|> reserved "symm"
  Sym <$> innerExpr

reflExpr = do
  reserved "refl"
  return $ Refl

transExpr = do
  reserved "trans"
  Trans <$> innerExpr <*> innerExpr


natExpr = do
  i <- integer
  return $ nums !! (fromInteger i)

  where nums = iterate s z
        s x = App (Con (string2Name "S")) Dynamic x
        z = Con (string2Name "Z")



convExpr = do
  reserved "conv"
  a <- expr
  (convBasic a <|> convContext a)
 <?> "Conv expression"

  where convBasic a = do
             -- Basic-style conversion syntax, where the proofs and holes are
             -- separate. Since the context-style seems to be the preference,
             -- we'll support this for backward compatibility by just
             -- translating to the context style.
             reserved "by"
             bs <- commaSep1 expr
             reserved "at"
             xs <- many1 varName
             dot
             c <- expr
             -- return $ Conv a bs (bind xs c)
             return $ ConvCtx a (substs [(n,Escape p) | n <- xs | p <- bs] c)
         -- Context-style conversion syntax
        convContext a = do
             reserved "at"
             ctx <- expr
             return $ ConvCtx a ctx


recExpr = do
  reserved "rec"
  f <- varName
  tele <- telescope
  -- u <- brackets termName
  reservedOp "."
  body <- expr
  return $ Rec (bind (f,tele) body)
 <?> "Rec expression"


indExpr = do
  reserved "ind"
  f <- varName
  -- (x,ty) <- parens $ (,) <$> varName <* colon <*> expr
  tele <- telescope
  u <- braces varName
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

existsExpr = do
  reserved "exists"
  (x,ty) <- parens $ (,) <$> varName <* colon <*> expr
  dot
  body <- expr
  return (Exists (bind (x,Embed ty) body)) <?> "Exists expression"

packExpr = do
  reserved "pack"
  e1 <- expr
  comma
  e2 <- expr
  return $ EIntro e1 e2

unpackExpr = do
  reserved "unpack"
  scrutinee <- expr
  reserved "as"
  bindings <- (parens $ (,) <$> varName <* comma <*> varName) <?>  "Exists elim binding"
  reserved "in"
  body <- expr
  return $ EElim scrutinee (bind bindings body)

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

formula = reserved "Formula" >> (Formula <$> option 0 integer)
sepType = reserved "Type" >> return Type

-- FIXME: Relatively certain this will cause the parser to choke.
ordExpr = reserved "ord" >> Ord <$> innerExpr
ordTrans = reserved "ordtrans" >> OrdTrans <$> innerExpr <*> innerExpr

-- FIXME: There's overlap between 'piType' and 'parens expr', hence the
-- backtracking. The 'piType' production should be moved to be a binop in expr.
innerExpr = wrapPos $
        (choice [
               (try natExpr <?> "Natural Number") -- Syntactic sugar for
                                         -- repeated iterations of S
              ,sepType <?> "Type"
              ,formula <?> "Form"
              ,abstraction
              ,quantification
              ,caseExpr
              ,termCase
              ,explicitPi
              ,try piType
              ,joinExpr
              ,contraExpr
              ,abortExpr
              ,showExpr
              ,contraAbortExpr
              ,convExpr
              ,recExpr
              ,indExpr
              ,recExpr
              ,valExpr
              ,tcastExpr
              ,ordExpr
              ,ordTrans
              ,letExpr
              ,escapeExpr
              ,strictExpr
               -- Existentials
              ,existsExpr
              ,packExpr
              ,unpackExpr

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
  where arg = ((,) Static <$> brackets expr) <|>
              ((,) Dynamic <$> innerExpr)
        mkApp f (s,a) = App f s a


expr = do
  st <- getState
  wrapPos $ exprParser st


-- The initial expression parsing table.
initialTable =
  [[binOp AssocNone "=" Equal]
  ,[binOp AssocNone "<" IndLT]
  ,[postOp "!" Terminates]
  ,[binOp AssocLeft ":" Ann]
  ,[binOp AssocRight "->"
    (\d r -> Pi Dynamic (bind (wildcard,Embed d,False) r))
   ,binOp AssocRight "=>"
    (\d r -> Pi Static (bind (wildcard,Embed d,False) r))]
  ]

binOp assoc op f = Infix (reservedOp op >> return f) assoc
postOp op f = Postfix (reservedOp op >> return f)
preOp op f = Prefix (reservedOp op >> return f)


-- sepOperator
sepOperator = do
  r <- choice [reserved i >> return i
               | i <- ["infix","infixr","infixl","pre","post"]
               ]
  level <- fromInteger <$> integer
  op <- operator
  -- update the table

  st <- getState
  let table' = IM.insertWith (++) level [toOp op r] $ exprOpTable st
      expr' = buildExpressionParser (map snd (IM.toAscList table')) factor
  putState $ ExprParserState expr' table'

  return (OperatorDecl op level r)
  where toOp op "infix" =
          binOp AssocNone op (binApp op)
        toOp op "infixr" =
          binOp AssocRight op (binApp op)
        toOp op "infixl" =
          binOp AssocLeft op (binApp op)
        toOp op "pre" =
          preOp op (App (Var (string2Name op)) Dynamic)
        toOp op "post" =
          preOp op (App (Var (string2Name op)) Dynamic)
        binApp op x y = App (App (Var (string2Name op)) Dynamic x) Dynamic y





wildcard = string2Name "_"


wrapPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y


telescope = do
  ps <- many1 piBinding
  return $ teleFromList ps
 <?> "telescope"

-- Parameters marked with ? before a name are supposed to be inferred.
infOption = option False $ (reservedOp "?" >> return True)

-- Flag handling
sepFlag = do
  reserved "flag"
  id <- identifier
  unless (id `elem` map fst flags) $
    unexpected $ id ++ " is an unknown flag." ++ "\n" ++
                 "Valid Flags:\n" ++
                 unlines (map fst flags)
  b <- ((reserved "true" >> return True) <|> (reserved "false" >> return False))
  return $ FlagDecl id b
  <?> "flag"
