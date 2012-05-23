module Parser where

import Names
import Syntax2
import BaseTypes
import Terms2(applyE,expTuple,listExp,truePat,falsePat
            ,patTuple,consExp,binop)
import Value(preDefinedDeclStrings)

import Monads(fmapM)
-- import Types(listT,tunit,pairT,tarr,predefinedTyCon,kindOf
--             ,toTyp,tupleT,arrT,applyT,showK,showT,nat)

import qualified System.IO
import qualified System.IO.Error
import Data.List(groupBy)

import Data.Char(digitToInt,isUpper)

-- These are for defining parsers
import Text.ParserCombinators.Parsec  
import Text.ParserCombinators.Parsec.Language(javaStyle,haskellStyle)
import Text.ParserCombinators.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Language.Trellys.LayoutToken -- Replaces Text.ParserCombinators.Parsec.Token
                   -- and adds layout rule parsing capability
import Debug.Trace
-----------------------------------------------
-- running parsers

parse1 file x s = runParser (whiteSp >> x) initState file s

parseWithName file x s =
  case parse1 file x s of
   Right(ans) -> ans
   Left message -> error (show message)
   
parse2 x s = parseWithName "keyboard input" x s   

parse3 p s = putStrLn (show state) >> return object
  where (object,state) = parse2 (do { x <- p; st <- getState; return(x,st)}) s

parseState p = (do { x <- p; (state,_) <- getState; return(x,state)})
    
parseString x s =
  case parse1 s x s of
   Right(ans) -> return ans
   Left message -> fail (show message)   

-- A special parser-transformer for seeing what input is left

observeSuffix x = 
  (do { a <- x; (col,tabs,left) <- getInfo; return(a,col,tabs,take 20 left)})

ps x s = parse2 (observeSuffix x) s

parseFile parser file =
  do {  possible <- System.IO.Error.try (readFile file)
     ; case possible of
         Right contents -> 
            case runParser (whiteSp >> parser) initState file contents of
              Right ans -> return ans
              Left message -> error(show message)
         Left err -> error(show err) }

--------------------------------------------         
-- Internal state and the type of parsers

type InternalState = (([(String, Typ)]   -- Map of a name of a TyCon and the TyCon (which includes its kind)
                      ,[(Name,Kind)])    -- Map of a TyVar to its kind
                     ,[Column]           -- column info for layout. This is fixed by "makeTokenParser" 
                     )
initState = ((predefinedTyCon,[]),[])
-- use (updateState,setState,getState) to access state

traceP p = do { ((c,vs),_) <- getState; ans <- p; ((d,us),_) <- getState
              ; trace ("In  "++show c++"\nOut "++show d) (return ans)}          
  

type MParser a = GenParser Char InternalState a

lbStyle = haskellStyle{reservedNames = 
                         ["if","then","else","case","of","let","in"
                         ,"data","gadt","synonym"
                         ,"mcata","mhist","mprim","msfcata","msfprim","where","with","Mu","In","forall","deriving"
                         ]
                      ,identStart = lower
                      }
                      
(funlog,LayFun layout) = makeTokenParser lbStyle "{" ";" "}"

lexemE p    = lexeme funlog p
arrow       = lexemE(string "->")
larrow      = lexemE(string "<-")
dot         = lexemE(char '.')
under       = char '_'
parenS p    = between (symboL "(") (symboL ")") p
braceS p    = between (symboL "{") (symboL "}") p
symboL      = symbol funlog
natural     = lexemE(number 10 digit)
whiteSp     = whiteSpace funlog
ident       = identifier funlog
sym         = symbol funlog
keyword     = reserved funlog
commA       = comma funlog
resOp       = reservedOp funlog
oper        = operator funlog
exactly s   = do { t <- ident; if s==t then return s else unexpected("Not the exact name: "++show s)}

number ::  Integer -> MParser Char -> MParser Integer
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
        ; seq n (return n)
        }
        
-------------------- Names and identifiers --------------------------

-- conName :: MParser String
conName = lexeme funlog (try construct)
  where construct = do{ c <- upper
                      ; cs <- many (identLetter lbStyle)
                      ; if (c:cs) == "Mu" 
                           then fail "Mu"
                           else return(c:cs)}
                    <?> "Constructor name"
                    
nameP = do { pos <- getPosition; x <- ident; return(Nm(x,pos))}
conP = do { pos <- getPosition; x <- conName; return(Nm(x,pos))}

patvariable :: MParser (Pat Name PTyp)
patvariable = 
  do { x <- nameP
     ; let result = (PVar x)
     ; let (patname@(init:_)) = name x
     ; if isUpper init
          then fail ("pattern bindings must be lowercase, but this is not: " ++ patname)
          else return result}

expvariable  :: MParser PExpr               
expvariable = escape <|> (do { s <- nameP; return(PEVar UNIV s)})
  where escape = do { char '`'; s <- nameP; return(PEVar GLOBAL s)}
        

expconstructor  :: MParser PExpr
expconstructor = do { nm <- conP; return(PECon nm) }
    -- pos <- getPosition; s <- conName; return(EVar (Nm(s,pos)))}
      
kindvariable  :: MParser Kind               
kindvariable = do { s <- nameP; return(Kname s)}

tycon = do { c <- conP; (name2Typ c)}  

badpolykind = PolyK [] badkind
badkind = LiftK (TyCon None (toName "OOPs") (PolyK [] Star))

-- name2Typ (Nm("Nat",_)) = return nat
name2Typ (name@(Nm(c,_))) = return (PTyCon name)
typevariable = do { nm <- nameP; return(PTyVar nm) }        
        
---------------------------------------------------------
-- Parsers for Literals

signed p = do { f <- sign; x <- p; return(f x) }
  where sign = (char '~' >> return negate) <|>
               (return id)   
               
chrLit  = do{ c <- charLiteral funlog; return (LChar c) }
doubleLit = do { n <- (signed (float funlog)); return(LDouble n)}
intLit = do{ c <- (signed Parser.natural); return (LInt (fromInteger c)) }
strLit = do{ pos <- getPosition
           ; s <- stringLiteral funlog
           ; let f c = PELit pos (LChar c)
           ; return(listExp (map f s))}
 
literal :: MParser Literal
literal = lexeme funlog
   (try doubleLit)  <|>  -- float before natP or 123.45 leaves the .45
   (try intLit)     <|>  -- try or a "-" always expects digit, and won't fail, "->"
   -- (try strLit)     <|>
   chrLit           <?> "literal"

--------------------- Parsing Patterns ----------------------------

simplePattern :: MParser (Pat Name PTyp)
simplePattern =
        tuplePattern
    <|> (do { pos <- getPosition; x <- literal; return(PLit pos x)}) 
    <|> (do { pos <- getPosition; sym "_"; return (PWild pos)})
    <|> (do { nm <- conP; return(PCon nm []) })
 --   <|> listPattern  -- in mendelr this matches with In so must be forbidden
    <|> patvariable
    <?> "simple pattern"

-- () (x)  (x,y,z)
tuplePattern = 
  do { xs <- parenS(sepBy pattern (commA))
     ; return(patTuple xs) 
     }

infixPattern =
  do { p1 <- try conApp <|> simplePattern
                    --  E.g. "(L x : xs)" should parse as ((L x) : xs) rather than (L(x:xs))
     ; x <- sym ":"
     ; pos <- getPosition; 
     ; p2 <- pattern
     ; return (PCon (Nm(x,pos)) [p1,p2])
     }

conApp =
   (do { nm <- conP 
       ; ps <- many simplePattern
       ; return(PCon nm ps)})
       
-- [2,3,4]  list pattersn imply use of 'out'
-- listPattern = 
--   do { xs <- brackets funlog (sepBy pattern (commA))
--      ; return(pConsUp patNil xs)
--      }

pattern :: MParser (Pat Name PTyp)
pattern = try infixPattern
  <|> conApp
  <|> simplePattern
  <?> "pattern"

-------------------------------------------------------------

------------------------------------------------------
-- Defining Infix and Prefix operators
-- See  "opList"  in Syntax.hs

operatorTable :: [[Operator Char InternalState PExpr]]
operatorTable = opList prefix infiX    

prefix :: String -> Operator Char InternalState PExpr
prefix name = Prefix(do{ try (resOp name); exp2exp name })   
  where -- exp2exp:: String -> Expr -> Expr
        exp2exp "~" = return neg
        exp2exp other = fail ("Unknown prefix operator: "++other)
        neg (PELit p (LInt x)) = PELit p (LInt (negate x))
        neg (PELit p (LDouble x)) = PELit p (LDouble (negate x))
        neg x = (PEApp (PEVar GLOBAL (Nm("negate",prelude))) x)

infiX nam assoc = 
   Infix (do{ pos <- getPosition; try (resOp nam); exp2exp2exp pos nam}) assoc
  where exp2exp2exp loc ":" = return consExp
        exp2exp2exp loc "$" = return (\ x y -> PEApp x y)
        exp2exp2exp loc nam = return (binop (Nm(nam,loc)))

infixExpression:: MParser PExpr
infixExpression =  buildExpressionParser operatorTable applyExpression

-- f x (3+4) 9
applyExpression:: MParser PExpr
applyExpression =
    do{ exprs <- many1 simpleExpression
      ; return (applyE exprs)
      }  
      
-------------------------------
simpleExpression :: MParser PExpr
simpleExpression = 
        parenExpression           -- (+) () (x) (x,y,z)
    <|> literalP                  -- 23.5   'x'   `d  123  #34 45n  
    <|> strLit                    -- "abc"
    <|> listExpression            -- [2,3,4]
    <|> caseExpression            -- case e of {p -> e; ...}
    <|> mendlerExp
    <|> expconstructor            -- a constructor name like "Node" or "Cons"
    <|> expvariable               -- names come last
    <?> "simple expression"

-- 23.5   123  "abc"  ()
literalP = do { loc <- getPosition; x <- literal; return(PELit loc x)}

-- (,)
pairOper :: MParser PExpr
pairOper = do { l <- getPosition
              ; parenS commA
              ; return (PEAbs ElimConst
                             [(PVar (Nm("_x",l))
                              ,PEAbs ElimConst
                                    [(PVar (Nm("_y",l))
                                     ,PETuple[PEVar UNIV (Nm("_x",l)),PEVar UNIV (Nm("_y",l))])])])}
                                     
-- (+), (* 5) (3 +) (,) etc
section :: MParser PExpr
section = try operator <|> try left <|> try right <|> try pairOper
  where operator = (do { l <- getPosition
                       ; sym "("; z <- oper; sym ")"
                       ; return (PEAbs ElimConst
                                      [(PVar (Nm("_x",l))
                                      ,PEAbs ElimConst
                                            [(PVar (Nm("_y",l))
                                             ,applyE [PEVar UNIV (Nm(z,l))
                                                     ,PEVar UNIV (Nm("_x",l))
                                                     ,PEVar UNIV (Nm("_y",l))] )])])})
        left =(do { l <- getPosition
                  ; sym "("; z <- oper; y <- expr; sym ")"
                  ; return (PEAbs ElimConst
                                 [(PVar (Nm("_x",l))
		                  ,applyE [PEVar UNIV (Nm(z,l)), PEVar UNIV (Nm("_x",l)) ,y])])})
        right = (do { l <- getPosition
                    ; sym "("; y <- simpleExpression; z <- oper; sym ")"
                    ; return (PEAbs ElimConst
                                   [(PVar (Nm("_x",l))
		                   ,applyE [PEVar UNIV (Nm(z,l)),y,PEVar UNIV (Nm("_x",l))])])})
		                   
-- () (x) (x,y,z) (+) (+ 3) (3 *) (,) etc
parenExpression ::  MParser PExpr
parenExpression = try section <|> tuple  
  where tuple = 
          do { xs <- parenS(sepBy expr (commA))
             ; return(expTuple xs)}		                   
	                                           
                                     
-- [2,3,4]
listExpression :: MParser PExpr
--listExpression = 
--  do { xs <- brackets funlog (sepBy expr (commA))
--     ; return(listExp xs)}
     
listExpression = (try empty) <|> (do { sym "["; x <- expr; tail x })
  where empty = do { sym "["; sym "]"; return (listExp [])}
        tail x = more x -- <|> count x <|> comp x
        more x = (sym "]" >> return(listExp [x])) <|>
                 (do { xs <- many (sym "," >> expr)
                     ; sym "]"
                     ; return(listExp (x:xs))})
{-                     
        count i = do { sym ".."; j <- expr; sym "]"
                     ; return(EComp(Range i j))}
        comp x = do { sym "|"
                    ; xs <- sepBy bind (symboL ",")
                    ; sym "]"
                    ; return(EComp(Comp x xs))}
        bind = try gen <|> fmap Pred expr
        gen = do { p <- pattern
                 ; sym "<-"
                 ; e <- expr
                 ; return(Generator p e)}
-}                             
     
     
-- \ x -> f x
lambdaExpression :: MParser PExpr
lambdaExpression =
    do{ resOp "\\"
      ; e2 <- elim nameP
      ; xs <- layout arm (return ())
      ; return(PEAbs e2 xs) }

arm:: MParser (Pat Name PTyp,PExpr)
arm = do { pat <- pattern
         ; sym "->"
         ; e <- expr
         ; return(pat,e) }     

-- if x then y else z
ifExpression :: MParser PExpr
ifExpression =
   do { keyword "if"
      ; e1 <- expr
      ; keyword "then"
      ; l1 <- getPosition
      ; e2 <- expr
      ; keyword "else"
      ; l2 <- getPosition
      ; e3 <- expr
      ; return(PEApp (PEAbs ElimConst [(truePat,e2),(falsePat,e3)]) e1)
      }
      
-- case e of { p -> body; ... }
caseExpression:: MParser PExpr
caseExpression =
    do{ keyword "case"
      ; e2 <- elim nameP
      ; arg <- expr
      ; keyword "of"
      ; alts <- layout arm (return ())
      ; return(PEApp (PEAbs e2 alts) arg)
      }      

inExpression =
  do { f <- inP; x <- expr; return(f x)}
  
---------------------- Parsing Expr ---------------------------
e1 = parse2 expr "(123,34.5,\"abc\",())"
e2 = parse2 expr "if x then (4+5) else 0"
e3 = parse2 expr "case x of\n   D x -> 5\n   C y -> y+1"
e4 = parse2 expr "\\ C x -> 4\n  D y -> g 7 y"
e5 = parse2 expr "\\ x -> \\ y -> x+ y"

expr :: MParser PExpr
expr =  lambdaExpression
--     <|> letExpression
    <|> ifExpression
    <|> inExpression
    <|> infixExpression     --names last
    <?> "expression"



------------------------------------------
-- Note, other than data declarations all decls
-- start with:  --  pat* =  ...

decl:: MParser (Decl PExpr)
decl = (datadec <|> gadtdec <|> synP <|> dec) <?> "decl"

synP =   
  do { pos <- getPosition
     ; keyword "synonym"
     ; nm <- conP
     ; xs <- many nameP
     ; sym "="
     ; body <- typP -- typT (fmap Pattern (braceS pattern))  -- typPat
     ; return(Synonym pos nm xs body) }

-- datadec2:: MParser Decl
datadec = 
  do { pos <- getPosition
     ; keyword "data"
     ; nm <- conP
     ; let kinding = parenS explicit <|> implicit
           implicit = do { nm <- nameP; return(nm,Star)}
           explicit = do { v <- nameP ; sym "::"; k <- kindP; return (v,k)}
     ; args <- many kinding
     ; sym "=" 
     ; ((ts,vs),cols) <- getState
   
     ; cs <- sepBy constr (sym "|")
     ; ds <- derivs
     ; let ans = (DataDec pos nm (map fst args) cs ds)
  
     ; return ans } 
     
gadtdec = 
  do { pos <- getPosition
     ; keyword "gadt"
     ; nm <- conP
     ; sym ":"
     ; alls <- (do { keyword "forall"
                   ; zs <- sepBy nameP (sym ",")
                   ; sym "."; return zs})  <|> (return [])
     ; k <- kindP
     ; keyword "where"
    -- ; (old@((ts,vs),cols)) <- getState
    -- ; setState (((name nm,TyVar nm k):ts,vs),cols)  
     ; cs <- layout (constr2) (keyword "deriving" <|> return ())
     ; ds <- sepBy derivation (sym ",")
     ; return(GADT pos nm alls k cs ds)}

derivs = (do { keyword "deriving"; sepBy derivation (sym ",") }) <|> return []
derivation = do { sym "fixpoint"; fmap Syntax conName }

constr2 =
  do { c <- conP
     ; sym ":"
     ; let name = do { n <- nameP; return(n,Star)}
   --  ; freeTs <- (do { ns <- many1 name; sym "."; return ns}) <|> (return [])     
     ; (schs,rho) <- rhoParts
     ; return(c,[] {- map fst freeTs -},schs,rho)}
     
     

constr =
  do { c <- conP;
     ; xs <- many sch
     ; return(c,xs) }     

sch = try (parenS scheme) <|> (do { x <- simpleTypP; return(Sch [] (Tau x))})

ex1 = (parse2 scheme "forall a b c . IO (a -> b) -> IO a -> IO (b,c)")

ex2 = mapM (parse3 decl) preDefinedDeclStrings
ex3 = parse3 (datadec >> datadec) 
       "data F x (z:: * -> *) = C (z x) | D Integer x | E (forall (x::*) . z x)\ndata T = T  (F Integer)"


dec = undefined
{-
dec = do { pos <- getPosition
         ; lhs <- many1 simplePattern
         ; resOp "=" 
         ; case lhs of
            ((PVar f : (p:ps))) -> 
	        do { body <- expr; return(FunDec pos (name f) [] [(p:ps,body)]) }
	    ([p]) -> do { b <- expr; return(Def pos p b) }
	    ((PCon c []):ps) ->  do { b<- expr; return(Def pos (PCon c ps) b)} }
-}

program = do { whiteSp
             ; (ds,(tyConMap,vsMap)) <- parseState (layoutDecl (return ()))
             ; eof
             ; return (Prog ds)}

layoutDecl endtag = do { ds <- layout decl endtag
                       ; return(map merge (groupBy sameName ds)) }
  where sameName (FunDec p n _ _) (FunDec q m _ _) = n==m
        sameName _ _ = False
        merge:: [Decl PExpr] -> Decl PExpr
        merge [d] = d
        merge ((FunDec pos name ts ws):ms) = FunDec pos name ts (ws++ concat(map g ms))
        g (FunDec pos name ts ws) = ws
       

------------------------------------------------

---------------------------------------------------
-- parsing types have embedded terms, These terms
-- can be either (Parsed Expr) or (Pattern Pat)
-- simpleT, muT, typT, simpleKindT take a parser 
-- that specializes for a particular embedded Term.

typP :: MParser Typ
simpleTypP :: MParser Typ
-- firstOrderT :: MParser Typ

typP = undefined
simpleTypP = undefined
firstOrderT = undefined

----------

simplePTyp :: MParser PTyp
simplePTyp = mu <|> tycon <|> typevariable <|> special <|> parenS inside  
  where inside = allP <|> fmap pairs (sepBy ptypP (comma funlog)) 
        allP = do { keyword "forall"
                  ; x <- many nameP
                  ; sym "."
		  ; body <- ptypP
                  ; return(PTyAll x body)}
        pairs [] = ptunit
        pairs [x] = x
        pairs (x:xs) = PTyTuple (x:xs) 
        listT x = PTyApp (PTyMu Star) (PTyApp (PTyCon (pre "L")) x)
        special = (fmap listT (brackets funlog ptypP))  -- like [ Int ]
                  
mu = do { keyword "Mu"; k <- simplekindP; return(PTyMu k)}

applyPT [] = return ptunit
applyPT [Left t] = return t
applyPT (Right e : ts) = unexpected ("index type: {"++show e++"}\nUsed in a position which is not an argument to an indexed type constructor.")
applyPT (Left t: Left s:ts) = applyPT (Left(PTyApp t s) : ts)
applyPT (Left t: Right s: ts) = applyPT(Left(PTyIndex t s) : ts)

simpleEither = fmap Left simplePTyp <|> fmap Right (braceS expr)
                
ptypP :: MParser PTyp                   
ptypP = fmap arrow (sepBy1 (fmapM applyPT (many1 simpleEither)) (sym "->"))
  where arrow [x] = x
        arrow (x:xs) = PTyArr x (arrow xs)
                
firstOrderPT :: MParser PTyp
firstOrderPT = muApp <|> tyConApp 
  where tyConApp = do { m <- tycon
                      ; ts <- many simpleEither
                      ; (applyPT (Left m:ts)) }
        muApp = do { m <- mu
                   ; t <- construct
                   ; ts <- many simpleEither
                   ; (applyPT (Left m: Left t:ts))}
        construct = tycon <|> parenS tyConApp        


 		  
		  
                  


{-
simpleTypP :: MParser Typ
simpleTypP  = simpleT     (fmap Parsed (braceS expr))
typP        = typT        (fmap Parsed (braceS expr))
muP         = muT         (fmap Parsed (braceS expr))

firstOrderP = firstOrderT (fmap Parsed (braceS expr))

typPat = undefined

{-
  do { ty <- typT (fmap Pattern (braceS pattern))
     ; return(toPat ty)}
-}

simpleT p = muT p <|> tycon <|> typevariable <|> special <|> parenS inside  <|> fmap TyLift p
  where inside = fmap pairs (sepBy (typT p) (comma funlog))        
        pairs [] = tunit
        pairs [x] = x
        pairs (x:xs) = TyTuple Star (x:xs) -- pairT x (pairs xs)
        special = -- (try (sym "(,)") >> return tpair) <|>
                  -- (try (sym "(->)") >> return tarr) <|>
                  -- (try (sym "[]") >> return tlist)  <|>
                  (fmap listT (brackets funlog (typT p)))
                                       
-- typP :: MParser Typ

typT p = fmap arrow (sepBy1 (fmap applyT (many1 (simpleT p))) (sym "->"))
  where arrow [x] = x
        arrow (x:xs) = arrT x (arrow xs)
        

muT p = do { keyword "Mu"; k <- simplekindT p; return(TyMu k)}

firstOrderT p = muApp <|> tyConApp 
  where tyConApp = do { m <- tycon
                      ; ts <- many (simpleT p)
                      ; return (applyT (m:ts)) }
        muApp = do { m <- muT p
                   ; t <- construct
                   ; ts <- many (simpleT p)
                   ; return(applyT (m:t:ts))}
        construct = tycon <|> parenS tyConApp
-}

---------------------------------------------------------    

inP = do { keyword "In"; k <- simplekindP; return(PEIn k)}

simplekindP = simplekindT (fmap Parsed (braceS expr))

kindP       = kindT       (fmap Parsed (braceS expr))

simplekindT p = fmap (const Star) (sym "*") <|> 
              kindvariable <|>
              fmap LiftK (firstOrderT p) <|>
              try (parenS (kindT p))
              -- (do { t <- firstOrderType; return(LiftK t)}) 
              
kindT p = fmap arrow (sepBy1 (simplekindT p) (sym "->"))
  where arrow [x] = x
        arrow (x:xs) = Karr x (arrow xs)        
  
scheme = do { sym "forall"
            ; vs <- many1 kinding
            ; sym "."
            ; t <- typP
            ; return (Sch vs (Tau t))}
  where kinding = fmap lift nameP <|> parenS colon
        colon = do { v <- nameP ; sym "::"; k <- kindP; return (v,Type k)}
        lift x = (x,Type Star)

simpleRho = try (parenS scheme) <|> (do { t <- (fmap applyT (many1 simpleTypP)); return(Sch [] (Tau t))})

rhoP = do { ss <- sepBy1 simpleRho (sym "->")
          ; let g [Sch [] rho] = rho
                g [t@(Sch (v:vs) rho)] = error ("Scheme as final type of Rho: "++show t)
                g (s:ss) = Rarr s (g ss)
          ; return(g ss)}
          
rhoParts = 
  do { ss <- sepBy1 simpleRho (sym "->")
     ; let g [Sch [] rho] = ([],rho)
           g [t@(Sch (v:vs) rho)] = error ("Scheme as final type of Rho: "++show t)
           g (s:ss) = (s:xs,r) where (xs,r) = g ss
     ; return(g ss)}
--------------------------------------------------------

elim:: MParser x -> MParser (Elim [x])
elim xP = (do { sym "{"; more}) <|> return ElimConst
  where more = do { ns <- many1 xP
                  ; sym "."
                 -- ; ((ts,us),cols) <- getState
		 -- ; setState ((ts,(map (\ x -> (x,Star)) ns)++us),cols)
		  ; t <- typP
                 -- ; setState ((ts,us),cols)
                  ; sym "}"
                  ;return(ElimFun ns t)}

--------------------------------------------------------

mendlerOp = (keyword "mcata"  >> return "mcata") <|> 
            (keyword "mhist"   >> return "mhist") <|>
            (keyword "mprim"   >> return "mprim") <|>
            (keyword "msfcata" >> return "msfcata") <|>
            (keyword "msfprim" >> return "msfprim") <?> "mendler operator"
            
mendlerExp =
  do { s <- mendlerOp
     ; e1 <- elim simpleTypP
     ; arg <- expr
     ; keyword "with"
     ; ms <- layout mclause (return ())
     ; return(PEMend s e1 arg ms)}
     
mclause = 
  do { ps <- many1 simplePattern
     ; sym "="
     ; b <- expr
     ; return(ps,b)}
     
ex5 = (parseFile program "tests/data.men")     

parseExpr s = parseString expr s
