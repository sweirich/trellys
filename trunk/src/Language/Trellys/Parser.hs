{-# LANGUAGE PatternGuards, FlexibleInstances, FlexibleContexts #-}
-- | A parsec-based parser for the Trellys concrete syntax.
module Language.Trellys.Parser
  (
   parseModuleFile,
   parseModule,
   parseExpr
  )
  where

import Language.Trellys.Syntax

import Language.Trellys.GenericBind

import Text.Parsec hiding (State)
import Text.Parsec.Prim (ParsecT)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Language.Trellys.LayoutToken as Token

import Control.Applicative ( (<$>) )
import Control.Monad.Trans (lift)
import Control.Monad.Error hiding (join)
import Control.Monad.State hiding (join)

import Data.Char
import Data.List

{- current concrete syntax for the annotated language:
 
  levels:
     l ::= natural numbers
 
  theta:
     th ::= prog | log
 
  terms:
    a,b,A,B ::=
      Type l                   Universes
    | x                        Variables   (start with lowercase)
    | C                        Term, Type constructors (start with uppercase)
    | \ x . a                  Runtime lambda
    | \ [x] . a                Erased lambda
    | a b                      Runtime application
    | a [b]                    Erased application
    | let x [y] = a in b       Runtime let, default to log
    | let th x [y] = a in b    Runtime let, explicitly prog or log
    | let [x] [y] = a in b     Erased let, default to log
    | let th [x] [y] = a in b  Erased let, default to log
    | (x : A) -> B             Runtime, logical pi
    | (x : A) => B             Runtime, programmatic pi
    | [x : A] -> B             Erased, logical pi
    | [x : A] => B             Erased, programmatic pi
    | case a [y] of            Case expressions, roughly
        C1 [x] y z -> b1         
        C2 x [y]   -> b2
    | a = b                    Equality type
    | join k                   Equality proof
    | conv a by b at EqC       Conversion
    | conta a                  Contra
    | abort                    Abort
    | rec f x = a              Runtime rec
    | rec f [x] = a            Erased rec
    | recnat f x = a           Runtime natrec
    | recnat f [x] = a         Erased natrec
    | (a : A)                  Annotations
 
 
   equality contexts
     EqC ::= x. A
 
  telescopes:
    D ::=
                               Empty
     | (x : A) D               Logical, runtime cons
     | (prog x : A) D              Programmatic, runtime cons
     | [x : A] D               Logical, erased cons
     | [prog x : A] D              Programmatic, erased cons

  declarations:

    For logical declarations:
      foo : A
      foo = a

      or
      
      log foo : A
      foo = a

    For programmatic declarations:

      prog foo : A
      foo = A

    For axiom declarations:
      axiom prog foo : A -- programmatic
      axiom log  foo : A -- logical
      axiom foo : A      -- also logical
    
    For logical datatype declarations:

       data T D -> Type l where
         C1 : A1
         ...
         Cn : An
    
    For programmatic datatype declarations:
    
       data T D => Type l where
         C1 : A1
         ...
         Cn : An
    
 
  Syntax sugar:
 
   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

   - You can make a top level declaration a rec or recnat:

     foo : (n : Nat) -> A
     recnat foo x = ...

-}

-- | Parse a module declaration from the given filepath.
parseModuleFile :: String -> IO (Either ParseError Module)
parseModuleFile name = do
  putStrLn $ "Parsing File " ++ show name
  -- FIXME: Check to see if file exists. Resolve module names. Etc.
  contents <- readFile name
  return $ evalState (runParserT (do { whiteSpace; v <- moduleDef;eof; return v}) [] name contents) 0

  --parseFromFile (moduleDef >>= (\v -> eof >> return v)) name

-- | Parse a module from the given string.
parseModule :: String -> IO ()
parseModule input = do
  putStrLn $ "Parsing " ++ show input

-- | Test an 'LParser' on a String.
--
-- E.g., do
--
-- > testParser decl "axiom fix : (aTy : Type 0) -> (f : ((a:aTy) -> aTy)) -> aTy"
-- 
-- to parse an axiom declaration of a logical fixpoint combinator.
testParser :: (LParser t) -> String -> Either ParseError t
testParser parser str = evalState (runParserT (do { whiteSpace; v <- parser; eof; return v}) [] "<interactive>" str) 0

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser expr

data ParserState = ParserState {
                     tabs :: [Column], -- internal state for layout tabs.
                     nameSupply :: Integer -- source of fresh names
                   }

-- * Lexer definitions
type LParser a = ParsecT
                    String             -- The input is a sequence of Char
                    [Column]           -- The internal state for Layout tabs
                    (State Integer)    -- The internal state for generating fresh names.
                    a                  -- the type of the object being parsed

instance HasNext (ParsecT s u (State Integer))  where
  nextInteger = do
    x <- lift get
    lift (put (x+1))
    return (x+1)
  resetNext x = do
    lift (put x)

-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type.
trellysStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
trellysStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart	       = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , Token.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  ["join"
                  ,"rec"
                  ,"recnat"
                  ,"Type"
                  ,"data"
                  ,"where"
                  ,"case"
                  ,"of"
                  ,"with"
                  ,"abort"
                  ,"contra"
                  ,"conv", "by", "at"
                  ,"let", "in"
                  ,"prog", "log"
                  ,"axiom"
                  ]
               , Token.reservedOpNames =
                 ["!","?","\\",":",".", "=", "+", "-", "^", "()", "_"]
                }

tokenizer :: Token.GenTokenParser String [Column] (State Integer)
--layout:: LParser item -> LParser stop -> LParser [item]
(tokenizer,Token.LayFun layout) = Token.makeTokenParser trellysStyle "{" ";" "}"

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser Name
variable = 
  do i <- identifier
     case i of
       [] -> fail "Internal Error: empty identifier"
       (c : _) -> 
         if isUpper c 
           then fail "Expected a variable, but a constructor was found"
           else return $ string2Name i

wildcard :: LParser Name 
wildcard = reservedOp "_" >> fresh (string2Name "_")

variableOrWild :: LParser Name
variableOrWild = try wildcard <|> variable

constructor :: LParser Name
constructor =
  do i <- identifier
     case i of
       [] -> fail "Internal Error: empty identifier"
       (c : _) -> 
         if isLower c 
           then fail "Expected a constructor, but a variable was found"
           else return $ string2Name i

-- variables or constructors
varOrCon :: LParser Term
varOrCon = do i <- identifier
              let n = string2Name i
              case i of
                [] -> fail "Internal error: empty identifier"
                (c:_) -> if isUpper c then return (Con n) 
                                      else return (Var n)



colon, dot :: LParser ()
colon = Token.colon tokenizer >> return ()
dot = Token.dot tokenizer >> return ()

reserved,reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens,brackets :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer

natural :: LParser Integer
natural = Token.natural tokenizer

commaSep1 :: LParser a -> LParser [a]
commaSep1 = Token.commaSep1 tokenizer


natenc :: LParser Term
natenc =
  do n <- natural
     return $ foldr (\a b -> Paren (App Runtime a b)) 
                    (Con $ string2Name "Zero") 
                    (replicate (fromInteger n) (Con $ string2Name "Succ"))

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- string2Name <$> identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())
  return $ Module modName imports decls

importDef :: LParser ModuleImport
importDef = do reserved "import" >>  (ModuleImport <$> importName)
  where importName = string2Name <$> identifier


telescope :: LParser Telescope
telescope = many teleBinding
  where
    annot :: Epsilon -> LParser (Name,Term,Theta,Epsilon)
    annot ep =
      do th <- option Logic $ choice [reserved "prog" >> return Program,
                                      reserved "log"  >> return Logic]
         n <- variable
         colon
         ty <- expr
         return (n,ty,th,ep)

    teleBinding :: LParser (Name,Term,Theta,Epsilon)
    teleBinding =
      (    parens (annot Runtime)
       <|> brackets (annot Erased)) <?> "binding"
        where

eitherArrow :: LParser Theta
eitherArrow =     (reservedOp "->" >> return Logic)
              <|> (reservedOp "=>" >> return Program)


---
--- Top level declarations
---

decl,dataDef,axiomDef,sigDef,valDef,recNatDef,recDef :: LParser Decl
decl = dataDef <|> axiomDef <|> sigDef <|> valDef <|> recNatDef <|> recDef

-- datatype declarations.
dataDef = do
  reserved "data"
  name <- constructor
  params <- telescope
  th <- eitherArrow
  reserved "Type"
  level <- liftM fromInteger natural
  reserved "where"
  cs <- layout con (return ())
  return $ Data name params th level cs
  where con = do
            cname <- constructor
            colon
            ty <- expr
            return $ (cname,ty)
          <?> "Constructor"

axiomDef = do
  Axiom <$> (reserved "axiom" >> sigDef)

sigDef = do
  theta <- option Logic $
             (reserved "prog" >> return Program) <|>
             (reserved "log" >> return Logic)

  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  return $ Sig n theta ty

valDef = do
  n <- try (do {n <- variable; reservedOp "="; return n})
  val <- expr
  return $ Def n val

-- recursive nat definitions
recNatDef = do
  r@(NatRec _ b) <- recNat
  let ((n,_),_) = unsafeUnBind b
  return $ Def n r

-- recursive definitions
recDef = do
 r@(Rec _ b) <- rec
 let ((n,_),_) = unsafeUnBind b
 return $ Def n r



------------------------
------------------------
-- Annotated Terms
------------------------
------------------------


join :: LParser Term
join =
  do reserved "join"
     s1 <- optionMaybe $ liftM fromInteger natural
     s2 <- optionMaybe $ liftM fromInteger natural
     case (s1,s2) of
       (Nothing,Nothing) -> return $ Join 100 100
       (Just n,Nothing)  -> return $ Join n n
       (Just n1,Just n2) -> return $ Join n1 n2
       _                 -> error $ "Internal error: nat after no nat"

-- Expressions

expr,term,factor :: LParser Term
expr = do
    p <- getPosition
    Pos p <$> (buildExpressionParser table term)
  where table = [[ifix  AssocLeft "=" TyEq],
                 [ifixM AssocRight "=>" (mkArrow Program),
                  ifixM AssocRight "->" (mkArrow Logic)]
                ]
        ifix  assoc op f = Infix (reservedOp op >> return f) assoc
        ifixM assoc op f = Infix (reservedOp op >> f) assoc
        mkArrow th = do x <- fresh (string2Name "_")
                        return $ \tyA tyB -> Arrow th Runtime tyA (bind x tyB)

term = do -- This eliminates left-recursion in (<expr> := <expr> <expr>)
  f <- factor
  foldl' app f <$> many bfactor

  where bfactor = ((,) Erased  <$> brackets expr) <|>
                  ((,) Runtime <$> factor)
        app e1 (ep,e2)  =  App ep e1 e2

factor = choice [ varOrCon <?> "an identifier"
                , typen   <?> "Type n"
                , natenc <?> "a literal"
                , lambda <?> "a lambda"
                , recNat <?> "recnat"
                , rec    <?> "rec"
                , letExpr   <?> "a let"
                , contra    <?> "a contra"
                , caseExpr  <?> "a case"
                , convExpr  <?> "a conv"
                , join      <?> "a join"
                , impProd   <?> "an implicit function type"
                , expProdOrAnnotOrParens 
                    <?> "an explicit function type or annotated expression"
                ]

impBind,expBind :: LParser (Epsilon,Name)
impBind = brackets $ liftM ((,) Erased) variableOrWild
expBind = liftM ((,) Runtime) variableOrWild

impOrExpBind :: LParser (Epsilon,Name)
impOrExpBind = impBind <|> expBind


typen :: LParser Term
typen =
  do reserved "Type"
     n <- liftM fromInteger natural
     return $ Type n


-- Lambda abstractions have the syntax '\x . e' There is no type annotation
-- on the binder.
lambda :: LParser Term
lambda = do reservedOp "\\"
            binds <- many1 impOrExpBind
            dot
            body <- expr
            return $ foldr (\(ep,nm) m -> Lam ep (bind nm m))
                           body binds

-- recursive abstractions, with the syntax 'recnat f x = e', no type annotation.
recNat :: LParser Term
recNat = do
  reserved "recnat"
  n <- variable
  (stage,var) <- impOrExpBind
  reservedOp "="
  body <- expr
  return $ (NatRec stage (bind (n,var) body))

-- recursive abstractions, with the syntax 'rec f x = e', no type annotation.
rec :: LParser Term
rec = do
  reserved "rec"
  n <- variable
  (stage,var) <- impOrExpBind
  reservedOp "="
  body <- expr
  return $ (Rec stage (bind (n,var) body))

letExpr :: LParser Term
letExpr =
  do reserved "let"
     th <- option Logic $ choice [reserved "prog" >> return Program,
                                  reserved "log"  >> return Logic]
     (ep,x) <- impOrExpBind
     y <- brackets variableOrWild
     reservedOp "="
     boundExp <- expr
     reserved "in"
     body <- expr
     return $ (Let th ep boundExp (bind (x,y) body))

-- impProd - implicit dependent products
-- These have the syntax [x:a]->b or [a]->b .
impProd :: LParser Term
impProd =
  do (x,tyA) <- brackets (try (liftM2 (,) variableOrWild (colon >> expr))
                          <|> (liftM2 (,) (fresh (string2Name "_")) expr))
     th <- eitherArrow
     tyB <- expr
     return $ Arrow th Erased tyA (bind x tyB)

--FIXME: add wildcard

-- Product types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because explicit producs, annotations and
-- regular old parens all start with parens.
expProdOrAnnotOrParens :: LParser Term
expProdOrAnnotOrParens =
  let
    -- afterBinder picks up the arrow and the return type of a pi
    afterBinder :: LParser (Theta,Term)
    afterBinder = liftM2 (,) eitherArrow expr
    
    -- before binder parses an expression in parens
    -- If it doesn't involve a colon, you get (Right tm)
    -- If it does, you get (Left tm1 tm2).  tm1 might be a variable,
    --    in which case you might be looking at an explicit pi type.
    beforeBinder :: LParser (Either (Term,Term) Term)
    beforeBinder = parens $
      choice [do e1 <- try (term >>= (\e1 -> colon >> return e1))
                 e2 <- expr
                 return $ Left (e1,e2) 
             ,liftM Right expr]
  in
    do bd <- beforeBinder
       case bd of
         Left (Var x,a) ->
           option (Ann (Var x) a)
                  (do (th,b) <- afterBinder
                      return $ Arrow th Runtime a (bind x b))
         Left (a,b) -> return $ Ann a b
         Right a    -> return $ Paren a

caseExpr :: LParser Term
caseExpr = do
    reserved "case"
    e <- factor
    y <- brackets variableOrWild
    reserved "of"
    alts <- layout alt (return ())
    return $ Case e (bind y alts)
  where
    alt :: LParser (Name, Bind [(Name, Epsilon)] Term)
    alt =
      do c <- constructor
         bds <- many impOrExpBind
         let vs = map (\(a,b) -> (b, a)) bds
         reservedOp "->"
         body <- term
         return (c, bind vs body)

-- conv e0 to [x.t] with e1
-- XXX needs to be redone for contexts
convExpr :: LParser Term
convExpr = do
  reserved "conv"
  a <- expr
  reserved "by"
  bs <- commaSep1 expr
  reserved "at"
  xs <- many1 variable
  dot
  c <- expr
  return $ Conv a bs (bind xs c)

contra :: LParser Term
contra = do
  reserved "contra"
  witness <- expr
  return $ Contra witness

