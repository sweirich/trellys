{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-orphans #-}
module Language.SepPP.Parser (
  parseModule
) where

import Language.SepPP.Syntax
import Language.SepPP.Options

import Unbound.LocallyNameless hiding (name,Infix,Val,Con,Equal,Refl)

import Text.Parsec hiding (ParseError,Empty)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token

import Data.Typeable
import Control.Applicative hiding ((<|>),many)
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)
import Data.Char
import qualified Data.IntMap as IM




-- | Parse a string to module.
parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts = runParser sepModule initialParserState srcName cnts

-- User state, so that we can update the operator parsing table.
data ExprParserState =
  ExprParserState {
    exprParser :: Parsec String ExprParserState Expr,
    exprOpTable :: IM.IntMap [Operator String ExprParserState Identity Expr]
    }

initialParserState :: ExprParserState
initialParserState = ExprParserState {
  exprParser = buildExpressionParser initialTable factor,
  exprOpTable = IM.fromAscList (zip [0..] initialTable)
  }



-- | Lifting ParseErrors to Exceptions
deriving instance Typeable P.ParseError
instance Exception P.ParseError where

type Parser a = ParsecT String ExprParserState Identity a

-- | Parse an entire module

sepModule :: Parser Module
sepModule = do
  whiteSpace
  reserved "module"
  modName <- string2Name <$> identifier
  reserved "where"
  bs <- many1 sepDecl
  eof
  return $ Module modName bs


-- | Top-level binding
sepDecl :: Parser Decl
sepDecl = sepDataDecl <|> sepProgDecl <|> sepProofDecl <|> sepAxiomDecl <|>
          sepTheoremDecl <|> sepProgramDecl <|>
          sepInductiveDecl <|> sepRecursiveDecl <|>
          sepFlag <|> sepOperator

sepProgDecl :: Parser Decl
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


sepAxiomDecl :: Parser Decl
sepAxiomDecl = do
  reserved "axiom"
  n <- varName
  _ <- colon
  ty <- innerExpr
  return $ AxiomDecl n ty

sepProofDecl  :: Parser Decl
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

sepTheoremDecl :: Parser Decl
sepTheoremDecl = do
  reserved "Theorem"
  n <- varName
  _ <- colon
  reserved "forall"
  qvars <- many1 piBinding
  reservedOp "."
  ran <- expr
  reservedOp ":="
  body <- expr
  let form = foldr (\(_,(inf,vn,ty)) rest -> Forall (bind (vn,Embed ty,inf) rest)) ran qvars
      term = foldr (\(_,(_,vn,ty)) rest -> Lambda Form Static (bind (vn,Embed ty) rest)) body qvars
  return $ ProofDecl n form term

sepProgramDecl  :: Parser Decl
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
  let pty = foldr (\(stage,(inf,vn,ty)) rest -> Pi stage (bind (vn,Embed ty,inf) rest)) ran qvars
      term = foldr (\(stage,(_,vn,ty)) rest -> Lambda Program stage (bind (vn,Embed ty) rest)) body qvars
  return $ ProgDecl n pty term
  where varOrOpName = varName <|> parens (string2Name <$> operator)

sepRecursiveDecl :: Parser Decl
sepRecursiveDecl = do
  reserved "Recursive"
  n <- varOrOpName
  colon
  tele <- telescope
  reservedOp "->"
  ran <- expr
  reservedOp ":="
  body <- expr
  let pty = fTele (\(vn,stage,ty,inf) rest -> Pi stage (bind (vn,ty,inf) rest)) ran tele
      term = Rec (bind (n,tele) body)
  return $ ProgDecl n pty term
  where varOrOpName = varName <|> parens (string2Name <$> operator)

sepInductiveDecl :: Parser Decl
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
  let ty2 = fTele (\(vn,_,ty,inf) rest -> Forall (bind (vn,ty,inf) rest)) ran tele2
      ty3 = Forall (bind (iv,Embed (Terminates (Var ind)),False) ty2)
      ty1 = fTele (\(vn,_,ty,inf) rest -> Forall (bind (vn,ty,inf) rest)) ty3 tele1
      terms2 = fTele (\(vn,_,ty,_) rest -> Lambda Form Static (bind (vn,ty) rest)) body tele2
  return $ ProofDecl n ty1 (Ind (bind (n,tele1,iv) terms2))

  where lastTele (TCons rebinding) =
          case unrebind rebinding of
            (pat,Empty) -> return pat
            (_,t@(TCons _)) -> lastTele t
        lastTele Empty = unexpected "Argument list for inductive definition must be non-empty"

sepDataDecl  :: Parser Decl
sepDataDecl = do
  reserved "data"
  n <- consName
  colon
  ps <- params
  reserved "Type"
  reserved "where"
  cs <- sepBy cons (reservedOp "|")  <?> "Constructor declaration"
  return $ DataDecl (Con n) (bind ps cs)

  where cons = do
                Con c <- constructor
                colon
                t <- expr
                return (c,t)
        params = option Empty $ do
                   ps <- many1 piBinding
                   reservedOp "->"
                   return $ foldr (\(st,(inf,n,ty)) r ->
                             TCons (rebind (n,st,Embed ty,inf) r))  Empty ps

-- Flag handling
sepFlag :: Parser Decl
sepFlag = do
  reserved "flag"
  ident <- identifier
  unless (ident `elem` map fst flags) $
    unexpected $ ident ++ " is an unknown flag." ++ "\n" ++
                 "Valid Flags:\n" ++
                 unlines (map fst flags)
  b <- ((reserved "true" >> return True) <|> (reserved "false" >> return False))
  return $ FlagDecl ident b
  <?> "flag"




-- Tokenizer definition
sepPPStyle :: GenLanguageDef String u Identity
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
            "injective","sym","symm","trans","refl", "tcast",
            "set", -- for flags
            "Theorem", "Program", "Inductive", "Recursive",
            "infix", "infixl", "infixr", "pre", "post",
            "exists","as","pack","unpack"
           ],
           Token.reservedOpNames = ["\\", "=>", "|","?",".",":="]
           }


tokenizer :: Token.GenTokenParser String u Identity
tokenizer = Token.makeTokenParser sepPPStyle

identifier :: ParsecT String u Identity String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u Identity ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u Identity ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u Identity String
operator = Token.operator tokenizer

colon :: ParsecT String u Identity String
colon = Token.colon tokenizer

-- semi :: ParsecT String u Identity String
-- semi = Token.semi tokenizer

integer :: ParsecT String u Identity Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u Identity a -> ParsecT String u Identity a
brackets = Token.brackets tokenizer

parens :: ParsecT String u Identity a -> ParsecT String u Identity a
parens  = Token.parens tokenizer

-- semiSep :: ParsecT String u Identity a -> ParsecT String u Identity [a]
-- semiSep = Token.semiSep tokenizer


braces :: ParsecT String u Identity a -> ParsecT String u Identity a
braces = Token.braces tokenizer

dot :: ParsecT String u Identity String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u Identity String
comma = Token.comma tokenizer


alts :: ParsecT String u Identity a -> ParsecT String u Identity [a]
alts p = do
     first <- option True (reservedOp "|">> return False)
     if first
       then sepBy1 p (reservedOp "|")
       else sepBy p (reservedOp "|")

-- name :: Rep a => Parser (Name a)
-- name = string2Name <$> identifier

-- varName :: Parser EName

varName :: ParsecT String u Identity (Name Expr)
varName = do
  n <- identifier
  when (null n || isUpper (head n)) $
       unexpected "Variable names must begin with a lowercase letter"
  return (string2Name n)

consName :: ParsecT String u Identity (Name Expr)
consName = do
  n <- identifier
  when (null n || isLower (head n)) $
       unexpected "Constructor names must begin with an uppercase letter"
  return (string2Name n)


piBinding :: Parser (Stage, (Bool, Name Expr, Expr))
piBinding =
    (((,) Static <$> (try $ brackets binding)) <?> "Static Argument Declaration") <|>
    (((,) Dynamic <$> (try $ parens binding)) <?> "Dynamic Argument Declaration") <|>
    (do { v <- variable; return(Dynamic,(False,wildcard,v))})
  where binding = try ((,,) <$> infOption <*> varName <* colon <*> expr) <|>
                  (do { e <- expr; return(False,wildcard,e)})

nestPi :: [(Stage, (Bool, EName, Expr))] -> Expr -> Expr
nestPi [] body = body
nestPi ((stage,(inf,n,ty)):more) body =
   Pi stage (bind (n,Embed ty,inf) (nestPi more body))

-- "Pi(x:A)(y:x)z(List y)(q:Z) -> z x y q"
-- means  "(x : A) -> (y1 : x) -> (_2 : z) -> (_3 : List y1) -> (q4 : Z) -> z x y1 q4"

explicitPi :: Parser Expr
explicitPi = do
  reserved "Pi"
  bindings <- many piBinding
  reservedOp "->"
  range <- expr
  return $ nestPi bindings range
  <?> "Dependent product type with explicit 'Pi'"

piType :: Parser Expr
piType = do
  (stage,(inf,n,ty)) <- absBinding
  reservedOp "->"
  range <- expr
  return $ Pi stage (bind (n,Embed ty,inf) range)
  <?> "Dependent product type"


absBinding :: Parser (Stage, (Bool, Name Expr, Expr))
absBinding =
    ((,) Static <$> brackets binding) <|>
    ((,) Dynamic <$> parens binding)
  where binding = (,,) <$> infOption <*> varName <* colon <*> expr


abstraction :: Parser Expr
abstraction = unicodeAbstraction <|> asciiAbstraction

asciiAbstraction :: Parser Expr
asciiAbstraction = do
  reservedOp "\\"
  args <- many absBinding
  kind <- (reservedOp "->" >> return Program)  <|>
           (reservedOp "=>" >> return Form)

  -- Formula are always static
  let g (stage,p) = if kind == Form then (Static,p) else (stage,p)
  body <- expr
  return $ nestLambda kind (map g args) body -- Lambda kind stage' (bind (n,Embed ty) body)

nestLambda :: Kind -> [(Stage, (t, EName, Expr))] -> Expr -> Expr
nestLambda _ [] body = body
nestLambda kind ((stage,(_,n,ty)):more) body =
   Lambda kind stage (bind (n,Embed ty) (nestLambda kind more body))

unicodeAbstraction :: Parser Expr
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


quantification :: Parser Expr
quantification = do
  reservedOp "?" <|> reservedOp "forall"
  pairs <- many quantBinding
  reservedOp "."
  body <- expr
  return $ nestForall pairs body -- Forall (bind (n,Embed ty) body)


quantBinding :: Parser (Bool, Name Expr, Expr)
quantBinding = parens $ (,,) <$> infOption <*> varName <* colon <*> expr

-- FIXME: The 'brackets' around termWitness are necessary because 'varName'
-- matches 'of'. This needs to be refactored.
caseExpr :: Parser Expr
caseExpr = do
  reserved "case"
  scrutinee <- expr
  consEq <- braces varName
  termWitness <- option Nothing (Just <$> expr)
  reserved "of"
  branches <- alts (alt <?> "case alternative")
  return $ Case scrutinee termWitness (bind consEq branches )
  where alt = do cons <- identifier
                 unless (isUpper (head cons)) $
                   unexpected "Pattern requires an uppercase constructor name"
                 vars <- many pvar
                 reservedOp "->"
                 body <- expr
                 return (bind (cons,vars) body)
        pvar = do var <- brackets varName
                  return (var,Static)
               <|>
               do var <- varName
                  return (var,Dynamic)


termCase :: Parser Expr
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


joinExpr :: ParsecT String u Identity Expr
joinExpr = do
  reserved "join"
  i0 <- integer
  i1 <- integer
  return $ Join i0 i1


morejoinExpr :: Parser Expr
morejoinExpr = do
  reserved "morejoin"
  Tactic <$> MoreJoin <$> braces (commaSep1 innerExpr)


valExpr :: Parser Expr
valExpr = (reserved "value" <|> reserved "valax") >> Val <$> innerExpr


tcastExpr :: Parser Expr
tcastExpr = reserved "tcast" >>TCast <$> innerExpr <* reserved "by" <*> innerExpr


-- FIXME: I think the 'at' annotations are unnecessary, if we have annotations.
contraExpr :: Parser Expr
contraExpr = do
  reserved "contra"
  t <- innerExpr
  return $ Contra t

contraAbortExpr :: Parser Expr
contraAbortExpr = do
  reserved "contraabort"
  t1 <- innerExpr
  -- reserved "using"
  t2 <- innerExpr
  return $ ContraAbort t1 t2

abortExpr :: Parser Expr
abortExpr = do
  reserved "abort"
  Abort <$> expr

showExpr :: Parser Expr
showExpr = do
  reserved "show"
  Show <$> expr

symExpr :: Parser Expr
symExpr = do
  reserved "sym" <|> reserved "symm"
  Tactic <$> Sym <$> innerExpr

reflExpr :: ParsecT String u Identity Expr
reflExpr = do
  reserved "refl"
  return $ Tactic Refl

transExpr :: Parser Expr
transExpr = do
  reserved "trans"
  Tactic <$> (Trans <$> innerExpr <*> innerExpr)


equivExpr :: ParsecT String u Identity Expr
equivExpr = do
  reserved "equiv"
  Tactic <$> Equiv <$> integer


autoconvExpr :: Parser Expr
autoconvExpr = do
  reserved "autoconv"
  Tactic <$> Autoconv <$> innerExpr

injectiveExpr :: Parser Expr
injectiveExpr = do
  reserved "injective"
  Tactic <$> Injective <$> innerExpr

natExpr :: ParsecT String u Identity Expr
natExpr = do
  i <- integer
  return $ nums !! (fromInteger i)

  where nums = iterate s z
        s x = App (Con (string2Name "S")) Dynamic x
        z = Con (string2Name "Z")


-- This 'conv' should be removed.
convExpr :: Parser Expr
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


recExpr :: Parser Expr
recExpr = do
  reserved "rec"
  f <- varName
  tele <- telescope
  -- u <- brackets termName
  reservedOp "."
  body <- expr
  return $ Rec (bind (f,tele) body)
 <?> "Rec expression"


indExpr :: Parser Expr
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


letdecls
  :: Parser [(Stage, Name Expr, Maybe (Name Expr), Expr)]
letdecls =
  semiSep1 (do (x,stage) <- nm
               y <- option Nothing (Just <$> brackets (string2Name <$> identifier) <?> "name for let-binding equality")
               reservedOp "="
               z <- expr
               return(stage,x,y,z))
  where nm =
          do ident <- brackets (string2Name <$> identifier)
             return (ident,Static)
          <|>
          do ident <- string2Name <$> identifier
             return (ident,Dynamic)

letExpr :: Parser Expr
letExpr = do
  reserved "let"
  decls <- letdecls
  reserved "in"
  body <- expr
  let letnest [] e = e
      letnest ((stage,x,y,z):ds) e = Let stage (bind (x,y,Embed z) (letnest ds e))
  return $ letnest decls body

escapeExpr :: Parser Expr
escapeExpr = do
  reservedOp "~"
  Escape <$> (variable <|> parens expr)

strictExpr :: Parser Expr
strictExpr = do
  reserved "aborts"
  Aborts <$> innerExpr

existsExpr :: Parser Expr
existsExpr = do
  reserved "exists"
  (x,ty) <- parens $ (,) <$> varName <* colon <*> expr
  dot
  body <- expr
  return (Exists (bind (x,Embed ty) body)) <?> "Exists expression"

packExpr :: Parser Expr
packExpr = do
  reserved "pack"
  e1 <- expr
  comma
  e2 <- expr
  return $ EIntro e1 e2

unpackExpr :: Parser Expr
unpackExpr = do
  reserved "unpack"
  scrutinee <- expr
  reserved "as"
  bindings <- (parens $ (,) <$> varName <* comma <*> varName) <?>  "Exists elim binding"
  reserved "in"
  body <- expr
  return $ EElim scrutinee (bind bindings body)

-- Expr Productions
variable :: Parser Expr
variable = do
  v <- varOrCon
  case v of
    Var _ -> return v
    _ -> fail "Expected variable name"

constructor :: Parser Expr
constructor = do
  c <- varOrCon
  case c of
    Con _ -> return c
    _ -> fail "Expected constructor name"

varOrCon :: Parser Expr
varOrCon = do
  ident@(i:_) <- identifier
  if isUpper i
     then return $ Con (string2Name ident)
     else return $ Var (string2Name ident)

formula :: Parser Expr
formula = reserved "Formula" >> (Formula <$> option 0 integer)

sepType :: Parser Expr
sepType = reserved "Type" >> return Type

-- FIXME: Relatively certain this will cause the parser to choke.
ordExpr :: Parser Expr
ordExpr = reserved "ord" >> Ord <$> innerExpr

ordTrans :: Parser Expr
ordTrans = reserved "ordtrans" >> OrdTrans <$> innerExpr <*> innerExpr

-- FIXME: There's overlap between 'piType' and 'parens expr', hence the
-- backtracking. The 'piType' production should be moved to be a binop in expr.
innerExpr :: Parser Expr
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
              ,equivExpr
              ,autoconvExpr
              ,injectiveExpr

              ,varOrCon <?> "Identifier"
              ,parens expr <?> "Parenthesized Expression"
              ] <?> "innerExpr")

factor :: Parser Expr
factor = do
  f <- innerExpr
  args <- many arg
  return $ foldl mkApp f args
  where arg = ((,) Static <$> brackets expr) <|>
              ((,) Dynamic <$> innerExpr)
        mkApp f (s,a) = App f s a

expr :: Parser Expr
expr = do
  st <- getState
  wrapPos $ exprParser st


-- The initial expression parsing table.
initialTable :: [[Operator String u Identity Expr]]
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


binOp
  :: Assoc -> String -> (a -> a -> a) -> Operator String u Identity a
binOp assoc op f = Infix (reservedOp op >> return f) assoc

postOp :: String -> (a -> a) -> Operator String u Identity a
postOp op f = Postfix (reservedOp op >> return f)

preOp :: String -> (a -> a) -> Operator String u Identity a
preOp op f = Prefix (reservedOp op >> return f)


-- | sepOperator allows new operators to be declared.
sepOperator :: Parser Decl
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
        -- Unreachable, since we guard with 'choice' above...
        toOp _ fx = error (fx ++ " is not a valid operator fixity.")
        binApp op x y = App (App (Var (string2Name op)) Dynamic x) Dynamic y



wildcard :: Name Expr
wildcard = string2Name "_"

wrapPos :: Parser Expr -> Parser Expr
wrapPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y

telescope :: Parser Tele
telescope = do
  ps <- many1 piBinding
  return $ teleFromList ps
 <?> "telescope"

-- Parameters marked with ? before a name are supposed to be inferred.
infOption :: Parser Bool
infOption = option False $ (reservedOp "?" >> return True)

