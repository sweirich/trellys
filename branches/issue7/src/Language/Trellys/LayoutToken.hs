{-# LANGUAGE ExistentialQuantification, RankNTypes
 #-}
-----------------------------------------------------------------------------
-- THIS is a MODIFIED VERSION of
   -- Modified to support layout combinators by Tim Sheard 7/27/09
   -- Find modified and added lines by searching for "--MOD"

-- Module      :  Text.ParserCombinators.Parsec.Token
-- Copyright   :  (c) Daan Leijen 1999-2001
-- License     :  BSD-style (see the file libraries/parsec/LICENSE)
-- 
-- Maintainer  :  daan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  non-portable (uses existentially quantified data constructors)
--
-- A helper module to parse lexical elements (tokens).
-- 
-----------------------------------------------------------------------------

module Language.Trellys.LayoutToken
  ( LanguageDef (..)
  , TokenParser (..)
  , LayoutFun(..)
  , makeTokenParser
  , getInfo
  ) where

import Data.Char (isAlpha,toLower,toUpper,isSpace,digitToInt)
import Data.List (nub,sort)
import Text.ParserCombinators.Parsec

import Text.ParserCombinators.Parsec.Token(LanguageDef(..),TokenParser(..))

-----------------------------------------------------------
-- Given a LanguageDef, create a token parser.
-----------------------------------------------------------
-- THIS :: LanguageDef st -> TokenParser st
makeTokenParser languageDef open sep close
    =(TokenParser{ identifier = identifier
                 , reserved = reserved
                 , operator = operator
                 , reservedOp = reservedOp
                        
                 , charLiteral = charLiteral
                 , stringLiteral = stringLiteral
                 , natural = natural
                 , integer = integer
                 , float = float
                 , naturalOrFloat = naturalOrFloat
                 , decimal = decimal
                 , hexadecimal = hexadecimal
                 , octal = octal
            
                 , symbol = symbol
                 , lexeme = lexeme
                 , whiteSpace = whiteSpace
             
                 , parens = parens
                 , braces = braces
                 , angles = angles
                 , brackets = brackets
                 , squares = brackets
                 , semi = semi
                 , comma = comma
                 , colon = colon
                 , dot = dot
                 , semiSep = semiSep
                 , semiSep1 = semiSep1
                 , commaSep = commaSep
                 , commaSep1 = commaSep1
                 } --MOD also return the layout combinator!
     ,LayFun layout)
    where
     
    -----------------------------------------------------------
    -- Bracketing
    -----------------------------------------------------------
    parens p        = between (symbol "(") (symbol ")") p
    braces p        = between (symbol "{") (symbol "}") p
    angles p        = between (symbol "<") (symbol ">") p
    brackets p      = between (symbol "[") (symbol "]") p

    semi            = symbol ";" 
    comma           = symbol ","
    dot             = symbol "."
    colon           = symbol ":"

    commaSep p      = sepBy p comma
    semiSep p       = sepBy p semi

    commaSep1 p     = sepBy1 p comma
    semiSep1 p      = sepBy1 p semi


    -----------------------------------------------------------
    -- Chars & Strings
    -----------------------------------------------------------
    -- charLiteral :: CharParser st Char
    charLiteral     = lexeme (between (char '\'') 
                                      (char '\'' <?> "end of character")
                                      characterChar )
                    <?> "character"

    characterChar   = charLetter <|> charEscape 
                    <?> "literal character"

    charEscape      = do{ char '\\'; escapeCode }
    charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



    -- stringLiteral :: CharParser st String
    stringLiteral   = lexeme (
                      do{ str <- between (char '"')                   
                                         (char '"' <?> "end of string")
                                         (many stringChar) 
                        ; return (foldr (maybe id (:)) "" str)
                        }
                      <?> "literal string")

    -- stringChar :: CharParser st (Maybe Char)
    stringChar      =   do{ c <- stringLetter; return (Just c) }
                    <|> stringEscape 
                    <?> "string character"
                
    stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

    stringEscape    = do{ char '\\'
                        ;     do{ escapeGap  ; return Nothing }
                          <|> do{ escapeEmpty; return Nothing }
                          <|> do{ esc <- escapeCode; return (Just esc) }
                        }
                        
    escapeEmpty     = char '&'
    escapeGap       = do{ many1 space
                        ; char '\\' <?> "end of string gap"
                        }
                        
                        
                        
    -- escape codes
    escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                    <?> "escape code"

    -- charControl :: CharParser st Char
    charControl     = do{ char '^'
                        ; code <- upper
                        ; return (toEnum (fromEnum code - fromEnum 'A'))
                        }

    -- charNum :: CharParser st Char                    
    charNum         = do{ code <- decimal 
                                  <|> do{ char 'o'; number 8 octDigit }
                                  <|> do{ char 'x'; number 16 hexDigit }
                        ; return (toEnum (fromInteger code))
                        }

    charEsc         = choice (map parseEsc escMap)
                    where
                      parseEsc (c,code)     = do{ char c; return code }
                      
    charAscii       = choice (map parseAscii asciiMap)
                    where
                      parseAscii (asc,code) = try (do{ string asc; return code })


    -- escape code tables
    escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
    asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2) 

    ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                       "FS","GS","RS","US","SP"]
    ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                       "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                       "CAN","SUB","ESC","DEL"]

    ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                       '\EM','\FS','\GS','\RS','\US','\SP']
    ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                       '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                       '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']


    -----------------------------------------------------------
    -- Numbers
    -----------------------------------------------------------
    -- naturalOrFloat :: CharParser st (Either Integer Double)
    naturalOrFloat  = lexeme (natFloat) <?> "number"

    float           = lexeme floating   <?> "float"
    integer         = lexeme int        <?> "integer"
    natural         = lexeme nat        <?> "natural"


    -- floats
    floating        = do{ n <- decimal 
                        ; fractExponent n
                        }


    natFloat        = do{ char '0'
                        ; zeroNumFloat
                        }
                      <|> decimalFloat
                      
    zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                         ; return (Left n)
                         }
                    <|> decimalFloat
                    <|> fractFloat 0
                    <|> return (Left 0)                  
                      
    decimalFloat    = do{ n <- decimal
                        ; option (Left n) 
                                 (fractFloat n)
                        }

    fractFloat n    = do{ f <- fractExponent n
                        ; return (Right f)
                        }
                        
    fractExponent n = do{ fract <- fraction
                        ; expo  <- option 1.0 exponent'
                        ; return ((fromInteger n + fract)*expo)
                        }
                    <|>
                      do{ expo <- exponent'
                        ; return ((fromInteger n)*expo)
                        }

    fraction        = do{ char '.'
                        ; digits <- many1 digit <?> "fraction"
                        ; return (foldr op 0.0 digits)
                        }
                      <?> "fraction"
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0
                        
    exponent'       = do{ oneOf "eE"
                        ; f <- sign
                        ; e <- decimal <?> "exponent"
                        ; return (power (f e))
                        }
                      <?> "exponent"
                    where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)


    -- integers and naturals
    int             = do{ f <- lexeme sign
                        ; n <- nat
                        ; return (f n)
                        }
                        
    -- sign            :: CharParser st (Integer -> Integer)
    sign            =   (char '-' >> return negate) 
                    <|> (char '+' >> return id)     
                    <|> return id

    nat             = zeroNumber <|> decimal
        
    zeroNumber      = do{ char '0'
                        ; hexadecimal <|> octal <|> decimal <|> return 0
                        }
                      <?> ""       

    decimal         = number 10 digit        
    hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
    octal           = do{ oneOf "oO"; number 8 octDigit  }

    -- number :: Integer -> CharParser st Char -> CharParser st Integer
    number base baseDigit
        = do{ digits <- many1 baseDigit
            ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
            ; seq n (return n)
            }          

    -----------------------------------------------------------
    -- Operators & reserved ops
    -----------------------------------------------------------
    reservedOp name =   
        lexeme $ try $
        do{ string name
          ; notFollowedBy (opLetter languageDef) <?> ("end of " ++ show name)
          }

    operator =
        lexeme $ try $
        do{ name <- oper
          ; if (isReservedOp name)
             then unexpected ("reserved operator " ++ show name)
             else return name
          }
          
    oper =
        do{ c <- (opStart languageDef)
          ; cs <- many (opLetter languageDef)
          ; return (c:cs)
          }
        <?> "operator"
        
    isReservedOp name =
        isReserved (sort (reservedOpNames languageDef)) name          
        
        
    -----------------------------------------------------------
    -- Identifiers & Reserved words
    -----------------------------------------------------------
    reserved name =
        lexeme $ try $
        do{ caseString name
          ; notFollowedBy (identLetter languageDef) <?> ("end of " ++ show name)
          }

    caseString name
        | caseSensitive languageDef  = string name
        | otherwise               = do{ walk name; return name }
        where
          walk []     = return ()
          walk (c:cs) = do{ caseChar c <?> msg; walk cs }
          
          caseChar c  | isAlpha c  = char (toLower c) <|> char (toUpper c)
                      | otherwise  = char c
          
          msg         = show name
          

    identifier =
        lexeme $ try $
        do{ name <- ident
          ; if (isReservedName name)
             then unexpected ("reserved word " ++ show name)
             else return name
          }
        
        
    ident           
        = do{ c <- identStart languageDef
            ; cs <- many (identLetter languageDef)
            ; return (c:cs)
            }
        <?> "identifier"

    isReservedName name
        = isReserved theReservedNames caseName
        where
          caseName      | caseSensitive languageDef  = name
                        | otherwise               = map toLower name

        
    isReserved names name    
        = scan names
        where
          scan []       = False
          scan (r:rs)   = case (compare r name) of
                            LT  -> scan rs
                            EQ  -> True
                            GT  -> False

    theReservedNames
        | caseSensitive languageDef  = sortedNames
        | otherwise               = map (map toLower) sortedNames
        where
          sortedNames   = sort (reservedNames languageDef)
                                 


    -----------------------------------------------------------
    -- White space & symbols
    -----------------------------------------------------------
    symbol name
        = lexeme (string name)

    lexeme p       
        = do{ x <- p; whiteSpace; return x  }    
    ws 
        | noLine && noMulti  = many (simpleSpace <?> "")
        | noLine             = many (simpleSpace <|> multiLineComment <?> "")
        | noMulti            = many (simpleSpace <|> oneLineComment <?> "")
        | otherwise          = many (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
        where
          noLine  = null (commentLine languageDef)
          noMulti = null (commentStart languageDef)   

    --simpleSpace = skipMany1 (eoln whiteSpace <|> satisfy isSpace)        
    --MOD  simpleSpace WAS MODIFIED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09
    simpleSpace =
         many1 (satisfy isSpace) 
    
    oneLineComment =
        do{ xs <- try (string (commentLine languageDef))
          ; ys <- many (satisfy (/= '\n'))
          ; return (xs++ys)
          }

    multiLineComment =
        do { xs <- try (string (commentStart languageDef))
           ; ys <- inComment
           ; return(xs++ys)
           }

    inComment 
        | nestedComments languageDef  = inCommentMulti
        | otherwise                = inCommentSingle
        
    inCommentMulti 
        =   do{ xs <- try (string (commentEnd languageDef)) ; return xs }
        <|> do{ xs <- multiLineComment; ys <-inCommentMulti; return(xs++ys) }
        <|> do{ xs <- many1 (noneOf startEnd); ys <- inCommentMulti; return(xs++ys) }
        <|> do{ y <- oneOf startEnd; ys <- inCommentMulti; return(y:ys) }
        <?> "end of comment"  
        where
          startEnd   = nub (commentEnd languageDef ++ commentStart languageDef)

    inCommentSingle
        =   do{ xs <- try (string (commentEnd languageDef)); return xs }
        <|> do{ xs <- many1 (noneOf startEnd); ys <- inCommentSingle; return(xs++ys) }
        <|> do{ x <- oneOf startEnd; xs <- inCommentSingle; return(x:xs) }
        <?> "end of comment"
        where
          startEnd   = nub (commentEnd languageDef ++ commentStart languageDef)
    
    layoutSep   = (symbol sep)   <?> ("inserted layout separator ("++sep++")")
    layoutEnd   = (symbol close) <?> ("inserted layout closing symbol("++close++")")
    layoutBegin = (symbol open)  <?> ("layout opening symbol ("++open++")")
   
    layout p stop =
	   (do { try layoutBegin; xs <- sepBy p (symbol ";") 
	       ; layoutEnd <?> "explicit layout closing brace"
	       ; stop; return (xs)}) <|>
           (do { indent; xs <- align p stop; return xs})
           
    align p stop = ormore <|> zero
      where zero = do { stop; option "" layoutSep; undent; return []}
	    ormore = do { x <- p
	                ; whiteSpace
	                ; (do { try layoutSep; xs <- align p stop; return (x:xs)}) <|>
	                  (do { try layoutEnd; stop; return([x])}) <|>
	                     -- removing indentation happens automatically
	                     -- in function whiteSpace
	                  (do { stop; undent; return ([x])})}
  
    whiteSpace =
       do { (col1,_,_) <- getInfo
          ; wsChars <- ws
          ; (col2,tabs,more) <- getInfo
          ; case (wsChars,tabs,more,compare col2 col1) of
              ([],_,_,_) -> return ()
              (_,[],_,_) -> return ()
              (_,_,[],_) -> -- No more input, close all the pending layout with '}'
                            setInfo (col2,[],concat(map (const close) tabs))
              (cs,p:ps,_,EQ) -> setInfo (col2-1,tabs,sep++more)
              (cs,p:ps,_,LT) -> let adjust (col,[],add) = setInfo(col,[],rev add more)
                                    adjust (col,p:ps,add)
                                       | col2 < p = adjust(col-1,ps,close:add)
                                       | col2== p = setInfo(col-1,p:ps,rev (sep:add) more)
                                       | col2 > p = setInfo(col,p:ps,rev add more)
                                    rev [] xs = xs
                                    rev (s:ss) xs = rev ss (s++xs)
                                in adjust (col2,p:ps,[])
              (cs,p:ps,_,GT) -> return ()
          }
          
     
    	       
          



--MOD --------------------------------------------------------------------
-- THE FOLLOWING WAS ADDED FOR LAYOUT TOKEN PARSERS by Tim Sheard 7/27/09

getInfo = 
   do { pos <- getPosition
      ; tabs <- getState
      ; tokens <- getInput
      ; return(sourceColumn pos,tabs,tokens) }

setInfo (col,tabs,tokens) =
  do { p <- getPosition
     ; setPosition (setSourceColumn p col)
     ; setState tabs
     ; setInput tokens }

indent =
  do { pos <- getPosition
     ; tabs <- getState
     ; setState (sourceColumn pos : tabs)
     }

undent =
  do { (p:ps) <- getState
     ; setState ps
     }
     
eoln whiteSpace = 
  do { c <- satisfy (=='\n')  -- c == '\n' to succeed
     ; (col,tabs@(p:ps),input) <- getInfo
     ; whiteSpace -- this may screw up the tabs, 
                  -- but use the old tabs, but the 
                  -- new column (col2) and input (cs)
     ; (col2,_,cs) <- getInfo
     ; case cs of
         [] -> -- No more input, close all the pending layout with '}'
               setInfo (col2,[],map (const '}') tabs)
         _  ->  case compare col2 p of
                  EQ -> setInfo (col2-1,tabs,';':cs)
                  GT -> setInfo (col2,tabs,cs)
                  LT -> let adjust prefix cs column [] = setInfo (column,[],rev prefix cs)
                            adjust prefix cs column (tabs @ (p:ps))
                              | col2==p = setInfo (column-1,tabs,rev (';':prefix) cs)
                              | col2<p  = adjust ('}':prefix) cs (column - 1) ps
                              | col2>p  = setInfo (column,tabs,rev prefix cs)
                            rev [] ys = ys
                            rev (x:xs) ys = rev xs (x:ys)
                        in  adjust [] cs col2 tabs
      ; return '\n' }    
      
data LayoutFun = 
   LayFun (forall a t. GenParser Char [Column] a
             -> GenParser Char [Column] t
             -> GenParser Char [Column] [a])          
          
-- End of added code          
--MOD --------------------------------------------------------------------
          
