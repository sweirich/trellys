

import Text.PrettyPrint hiding (parens,braces)
import qualified Text.PrettyPrint as PP
import Text.ParserCombinators.ReadP
-- import GHC.Read	 hiding (list)
import Data.Char
import Control.Monad(when)

type Name = String
type Expr = String

data Term = Var String
          | Pi String Term Term
          | Lam String Term Term
          | App Term [Term]
          | Star
          | Conv Term Term  Proof Proof
          | Self String Term
          | Proof Proof

data Proof = Refl
           | Unfold
           | Eval
           | SubstSelf
           | Trans [Proof]
           | Ctx Term



instance Show Term where
  show t = render $ prTerm t

instance Read Term where
  readsPrec i = readP_to_S exprParser


data Sigs = Sigs [Signature] deriving Show


instance Read Sigs where
  readsPrec i = readP_to_S sigsParser
  
data Signature =
   Sig Name [(Name,Term)] [(Name,Term)] [Constructor]
   deriving Show

instance Read Signature where
  readsPrec i = readP_to_S sigParser

data Constructor = Cons Name [(Name,Term)] Term deriving Show

data Group = FixGroup [(Name,Term,Term)]

-- From a signature, emit a selfstar datatype declaration.
outSig (Sig name params indices constructors) =
  prGroup (FixGroup (ty:cs))
  where ty = (name,tySig Star,tyDef)
        tySig = piTerm (params ++ indices) 
        tyDef = lamTerm (params ++ indices)
                  (Self "p" (Pi "C" elimPredType (tyCases tyRange)))

        elimPredType = piTerm (indices ++ [("wit", appHelper (Var name) (params ++ indices))])  Star

        patternTypes = (map (cpattern params) constructors) 
        tyCases = piTerm patternTypes
        defCases = lamTerm patternTypes
        tyRange =
          App (Var "C")
            (map (Var . fst) indices ++
            [(Conv (Var "p") (appHelper (Var name) (params ++ indices))
              Refl (mkTypeCastRHS (params ++  indices)))])

        caseNames = [nm ++ "Case" | Cons nm _ _ <- constructors]
        cs = map (mkConstructor params indices elimPredType caseNames defCases) constructors


mkTypeCastRHS args
    | len == 0 = Unfold
    | otherwise = Trans [Ctx (App (Proof Unfold) refls), Eval]
  where len = length args
        refls = replicate len (Proof Refl)
  
mkConstructor params indices elimPredType caseNames cases (Cons name args res) =
  (name,consType,consDef)
  where consType = piTerm params $
                   piTerm args res

        consDef =
          Conv (lamTerm params $
                 lamTerm args $
                 Lam "C" elimPredType $ 
                  cases $
                    App (Var (name ++ "Case"))
                      (map (Var . fst) args))
             consType consCastLHS consCastRHS

        consCastLHS = Ctx $ piTerm
                             [(n, Proof Refl) |
                              n <- map fst (params ++ args) ++
                                   "C":caseNames]
                             (Proof
                              (Ctx (App (Var "C")
                                    (replicate (length indices) (Proof Refl)  ++
                                     [Proof $
                                      mkTypeCastRHS (params ++ args)]))))

        consCastRHS = Ctx $
                      piTerm [(n, Proof Refl) | (n,_) <- params  ++ args]
                        (Proof castRHSpf)
        castRHSpf
          | null params = Trans [Unfold, SubstSelf]
          | otherwise = Trans [Ctx (App (Proof Unfold)
                                    (replicate (length (params ++ indices))
                                     (Proof Refl))), 
                               Eval,
                               SubstSelf]

          

cpattern [] (Cons nm [] _) =
  (nm ++ "Case", App (Var "C") [Var nm])

cpattern params (Cons nm types res) =
  (nm ++ "Case",
   piTerm types (App (Var "C")
                 (indices ++
                  [App (Var nm) (map (Var . fst) (params ++ types))])))
  where indices = case res of
                       App _ appArgs -> drop (length params) appArgs
                       _ -> []
                       

piTerm args end = foldr mkPi end args
  where mkPi (n,t) rest = Pi n t rest
lamTerm args end = foldr mkLam end args
  where mkLam (n,t) rest = Lam n t rest

appHelper f [] = f
appHelper f argsWithTypes = App f (map (Var . fst) argsWithTypes)
 
appArgs f [] = f
appArgs f args = PP.parens $ f <+> hsep (map (text . fst) args)


-- * Test cases

nat = Sig "nat" [] []
      [Cons "zero" [] (read "nat"),
      Cons "succ" [("n",read "nat")] (read "nat")]


list = Sig "list" [("A",read "*")] []
       [Cons "nil" [] (read "(list A)")
       ,Cons "cons" [("x",read "A"), ("xs",read "(list A)")] (read "(list A)")]

vec = Sig "vec" [("A", Star)] [("n",read "nat")]
        [Cons "vnil" [] (read "(vec A zero)"),
         Cons "vcons" [("m", read "nat"),
                       ("x",read "A"), ("xs",read "(vec A m)")]
                (read "(vec A (succ m))")
        ]

eq = Sig "eq" [("A",read "*"),("a",read "A")] [("b",read "A")]
     [Cons "eqrefl" [] (read "eq A a a")]


genTests :: IO ()
genTests = writeFile "genTests.sub" $ render $ vcat (map outSig testCases)
  where testCases = [nat,list,vec,eq]
            

testGen :: String -> IO ()
testGen iname = do
  cnts <- readFile (iname ++ ".data")
  let Sigs s = read cnts
  let output = render $ vcat (map outSig s)
  writeFile (iname ++ ".sub") output
  putStrLn output


-- * Parsing

-- | Parser for sepstar expressions
exprParser = do es <- many1 termParser
                case es of
                  [f] -> return f
                  f:fs -> return $ App f fs
               
termParser = (skipSpaces >> string "*" >> return Star) <++
             (do skipSpaces
                 string "\\"
                 skipSpaces
                 x <- munch isAlpha
                 skipSpaces
                 ty <- exprParser
                 string "."
                 body <- exprParser
                 return (Lam x ty body)
             ) <++
             (do skipSpaces
                 string "!"
                 skipSpaces
                 x <- munch isAlpha
                 skipSpaces
                 ty <- exprParser
                 string "."
                 body <- exprParser
                 return (Lam x ty body)
             )
             <++
             (do skipSpaces
                 string "self"
                 skipSpaces
                 n <- munch1 isAlpha
                 skipSpaces
                 string "."
                 body <- exprParser
                 return $ Self n body
             )
             
             <++
             (do skipSpaces
                 x <- munch1 isAlpha
                 when (x `elem` reserved) pfail
                 return (Var x))
             <++
             (do skipSpaces
                 string "conv"
                 s <- exprParser
                 skipSpaces
                 string "to"
                 to <- exprParser
                 skipSpaces
                 string "by"
                 skipSpaces
                 p1 <- proofParser
                 skipSpaces
                 string ","
                 skipSpaces
                 p2 <- proofParser
                 return $ Conv s to p1 p2
                 )
             <++
             parens exprParser

proofParser = (string "refl" >> return Refl) <++
              (string "unfold" >> return Unfold)

reserved = ["conv", "by", "at", "refl", "self","unfold", "data", "where"]

delimit l r p = between (skipSpaces >> string l) (skipSpaces >> string r) p
parens = delimit "(" ")"
braces = delimit "{" "}"

keyword s = skipSpaces >> string s
identifier = skipSpaces >> munch1 isAlpha

sigParser = do
  keyword "data"
  id <- identifier
  params <- many arg
  keyword ":"
  indices <- many arg
  keyword "where"
  cs <- braces (sepBy  consParser (keyword ";"))
  return $ Sig id params indices cs
  

arg = skipSpaces >>
      (parens $ do
        i <- identifier
        skipSpaces
        keyword ":"
        ty <- termParser
        return (i,ty))
  
consParser = do
  id <- identifier
  keyword ":"
  args <- many arg
  keyword "->"
  ret <- termParser
  return $ Cons id args ret

sigsParser = do
  sigs <- many1 sigParser
  return $ Sigs sigs
  


-- * Pretty printing

dot t1 t2 = cat [t1 <+> text ". ", nest 2 t2]

prTerm (Var v) = text v
prTerm (Pi x ty body) = (text "!" <> text x <+> colon <+> wrapParen ty) `dot` (prTerm body)
prTerm (Lam x ty body) = (text "\\" <> text x <+> colon <+> wrapParen ty) `dot` prTerm body
prTerm (App f args) = PP.parens $ prTerm f <+> hsep (map wrapParen args)
prTerm Star = text "*"
prTerm (Conv s to p1 p2) = text "conv" <+> prTerm s $$
                           (nest 2 $ sep
                                [text "to" <+> wrapParen to,
                                 text "by" <+> PP.parens (prProof p1) <+> comma,
                                 PP.parens (prProof p2)])
prTerm (Self n t) = text "self" <+> text n <+> text "." <+> prTerm t

prTerm (Proof p) = prProof p

wrapParen Star = prTerm Star
wrapParen t@(Var v) = prTerm t
wrapParen t@(App _ _) = prTerm t
wrapParen t@(Proof p) = prProof p
wrapParen t = PP.parens $ prTerm t


prProof Refl = text "refl"
prProof Unfold = text "unfold"
prProof (Trans ps) = brackets $ sep (punctuate (text ";") (map prProof ps))
prProof Eval = text "eval"
prProof SubstSelf = text "substself"
prProof (Ctx t) = prTerm t


prGroup (FixGroup defs) = text "Fix" <+>
   cat (punctuate comma [text n <+> colon <+> cat [prTerm ty <+> text "= ", prTerm def] | (n,ty,def) <- defs])





   