{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
-- http://stackoverflow.com/questions/3023439/parsing-indentation-based-syntaxes-in-haskells-parsec/3023615#3023615

module Language.SepPP.Layout
    ( laidout          -- repeat a parser in layout, separated by (virtual) semicolons
    , space            -- consumes one or more spaces, comments, and onside newlines in a layout rule
    , maybeFollowedBy
    , spaced           -- (`maybeFollowedBy` space)
    , LayoutEnv        -- type needed to describe parsers
    , defaultLayoutEnv -- a fresh layout
    , semi             -- semicolon or virtual semicolon
    ) where

import Control.Applicative ((<$>))
import Control.Monad (guard)

import Data.Char (isSpace)

import Text.Parsec.Combinator
import Text.Parsec.Pos
import Text.Parsec.Prim hiding (State)
import Text.Parsec.Char hiding (space)

data LayoutContext = NoLayout | Layout Int deriving (Eq,Ord,Show)

data LayoutEnv = Env
    { envLayout :: [LayoutContext]
    , envBol :: Bool -- if true, must run offside calculation
    }

defaultLayoutEnv :: LayoutEnv
defaultLayoutEnv = Env [] True

pushContext :: Stream s m c => LayoutContext -> ParsecT s LayoutEnv m ()
pushContext ctx = modifyState $ \env -> env { envLayout = ctx:envLayout env }

popContext :: Stream s m c => String -> ParsecT s LayoutEnv m ()
popContext loc = do
    (_:xs) <- envLayout <$> getState
    modifyState $ \env' -> env' { envLayout = xs }
  <|> unexpected ("empty context for " ++ loc)

getIndentation :: Stream s m c => ParsecT s LayoutEnv m Int
getIndentation = depth . envLayout <$> getState where
    depth :: [LayoutContext] -> Int
    depth (Layout n:_) = n
    depth _ = 0

pushCurrentContext :: Stream s m c => ParsecT s LayoutEnv m ()
pushCurrentContext = do
    indent <- getIndentation
    col <- sourceColumn <$> getPosition
    pushContext . Layout $ max (indent+1) col

maybeFollowedBy :: Stream s m c => ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m a
t `maybeFollowedBy` x = do t' <- t; optional x; return t'

spaced :: Stream s m Char => ParsecT s LayoutEnv m a -> ParsecT s LayoutEnv m a
spaced t = t `maybeFollowedBy` space

data Layout = VSemi | VBrace | Other Char deriving (Eq,Ord,Show)

-- TODO: Parse C-style #line pragmas out here
layout :: Stream s m Char => ParsecT s LayoutEnv m Layout
layout = try $ do
    bol <- envBol <$> getState
    whitespace False (cont bol)
  where
    cont :: Stream s m Char => Bool -> Bool -> ParsecT s LayoutEnv m Layout
    cont True = offside
    cont False = onside

    -- TODO: Parse nestable {-# LINE ... #-} pragmas in here
    whitespace :: Stream s m Char =>
        Bool -> (Bool -> ParsecT s LayoutEnv m Layout) -> ParsecT s LayoutEnv m Layout
    whitespace x k =
            try (string "{-" >> nested k >>= whitespace True)
        <|> try comment
        <|> do newline; whitespace True offside
        <|> do tab; whitespace True k
        <|> do (satisfy isSpace <?> "space"); whitespace True k
        <|> k x

    comment :: Stream s m Char => ParsecT s LayoutEnv m Layout
    comment = do
        string "--"
        many (satisfy ('\n'/=))
        newline
        whitespace True offside

    nested :: Stream s m Char =>
        (Bool -> ParsecT s LayoutEnv m Layout) ->
        ParsecT s LayoutEnv m (Bool -> ParsecT s LayoutEnv m Layout)
    nested k =
            try (do string "-}"; return k)
        <|> try (do string "{-"; k' <- nested k; nested k')
        <|> do newline; nested offside
        <|> do anyChar; nested k

    offside :: Stream s m Char => Bool -> ParsecT s LayoutEnv m Layout
    offside x = do
        p <- getPosition
        pos <- compare (sourceColumn p) <$> getIndentation
        case pos of
            LT -> do
                popContext "the offside rule"
                modifyState $ \env -> env { envBol = True }
                return VBrace
            EQ -> return VSemi
            GT -> onside x

    -- we remained onside.
    -- If we skipped any comments, or moved to a new line and stayed onside, we return a single a ' ',
    -- otherwise we provide the next char
    onside :: Stream s m Char => Bool -> ParsecT s LayoutEnv m Layout
    onside True = return $ Other ' '
    onside False = do
        modifyState $ \env -> env { envBol = False }
        Other <$> anyChar

layoutSatisfies :: Stream s m Char => (Layout -> Bool) -> ParsecT s LayoutEnv m ()
layoutSatisfies p = guard . p =<< layout

virtual_lbrace :: Stream s m Char => ParsecT s LayoutEnv m ()
virtual_lbrace = pushCurrentContext

virtual_rbrace :: Stream s m Char => ParsecT s LayoutEnv m ()
virtual_rbrace = try (layoutSatisfies (VBrace ==) <?> "outdent")

-- recognize a run of one or more spaces including onside carriage returns in layout
space :: Stream s m Char => ParsecT s LayoutEnv m String
space = do
    try $ layoutSatisfies (Other ' ' ==)
    return " "
  <?> "space"

-- recognize a semicolon including a virtual semicolon in layout
semi :: Stream s m Char => ParsecT s LayoutEnv m String
semi = do
    try $ layoutSatisfies p
    return ";"
  <?> "semi-colon"
  where
        p VSemi = True
        p (Other ';') = True
        p _ = False

lbrace :: Stream s m Char => ParsecT s LayoutEnv m String
lbrace = do
    char '{'
    pushContext NoLayout
    return "{"

rbrace :: Stream s m Char => ParsecT s LayoutEnv m String
rbrace = do
    char '}'
    popContext "a right brace"
    return "}"

laidout :: Stream s m Char => ParsecT s LayoutEnv m a -> ParsecT s LayoutEnv m [a]
laidout p = try (braced statements) <|> vbraced statements where
    braced = between (spaced lbrace) (spaced rbrace)
    vbraced = between (spaced virtual_lbrace) (spaced virtual_rbrace)
    statements = p `sepBy` spaced semi