{-# LANGUAGE GeneralizedNewtypeDeriving, NoMonomorphismRestriction,
             OverloadedStrings #-}

module Language.HokeyLog.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified Data.HashSet as HS
import qualified Data.ByteString.Char8 as B
import Data.Maybe
import Data.Monoid
import Data.String
import Language.HokeyLog.Syntax
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import Text.Trifecta
import Text.Trifecta.Result

import Control.Unification.IntVar
import Data.Functor.Identity

newtype PrologParser m a = PrologParser {
      runPrologParser :: m a
} deriving (Functor, Monad, Applicative, Alternative, CharParsing, Parsing)

prologCommentStyle = CommentStyle "" "" "%" False
prologVarStyle =
    IdentifierStyle "prolog variable"
                    upper
                    (alphaNum <|> oneOf "-_:")
                    mempty
                    Identifier
                    ReservedIdentifier
prologAtomStyle = prologVarStyle { _styleName = "prolog atom",
                                   _styleStart = lower }
prologPredStyle = prologAtomStyle { _styleName = "prolog predicate" }
prologOpStyle =
    IdentifierStyle "prolog operator"
                    empty
                    empty
                    (HS.fromList [":-", "=", "not "])
                    Identifier
                    ReservedOperator

instance CharParsing m => TokenParsing (PrologParser m) where
    someSpace = buildSomeSpaceParser (void space) prologCommentStyle

var,predicate :: (Monad m, CharParsing m, IsString s) => PrologParser m s
var = fromString <$> ident prologVarStyle
predicate = fromString <$> ident prologPredStyle

op = reserve prologOpStyle

var_or_val :: (Monad m, CharParsing m, IsString s) =>
              PrologParser m v -> PrologParser m (Either s v)
var_or_val v = Left <$> var <|> Right <$> v

atomp :: (Monad m, CharParsing m, IsString s) =>
         PrologParser m v -> PrologParser m (Atom v (Either s v))
atomp v = do f <- predicate
             args <- optional (parens (commaSep $ var_or_val v))
             return $ atom f (fromMaybe [] args)
          <|> unification v
unification v = do a <- var_or_val v
                   op "="
                   b <- var_or_val v
                   return $ atom "=" [a,b]
lit v = do m <- optional $ (op "not ")
           a <- atomp v
           return $ case m of
                      Nothing -> Pos a
                      _ -> Neg a

rule v = do h <- atomp v
            b <- optional (op ":-" >> commaSep1 (lit v))
            dot
            return $ h :- fromMaybe [] b

program v = some (rule v)
query v   = atomp v

value = Str <$> (predicate <|> fromString <$> stringLiteral)
        <|> Num . fromIntegral <$> integer

parse p s = case parseString (runPrologParser p) mempty s of
              Success a -> a
              Failure f -> error (show f)

-- parseFile :: PrologParser v a -> FilePath -> IO (Result a)
parseFile p f = do res <- parseFromFile (runPrologParser p) f
                   case res of
                     Just a -> return a
                     Nothing -> error "parse failure"

p = parse (program value)  "f(X, Y) :- g(X), h(Y).\
                            \g(1).\
                            \g(2).\
                            \g(3).\
                            \h(\"foo\").\
                            \h(3).\
                            \% Some commentary\n\
                            \h(4).\
                            \i(X, Y) :- f(X, Y), not f(Y, X)."

pv = mapM postvaricate p

q = postvaricate $ (parse $ query value) "i(A, B)"

