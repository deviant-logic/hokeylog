{-# LANGUAGE GeneralizedNewtypeDeriving, NoMonomorphismRestriction #-}

module Language.HokeyLog.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified Data.HashSet as HS
import Language.HokeyLog.Syntax
import Data.Monoid
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
    someSpace = buildSomeSpaceParser (skipSome space) prologCommentStyle

var,predicate :: (Monad m, CharParsing m) => PrologParser m String
var = ident prologVarStyle
predicate = ident prologPredStyle

op = reserve prologOpStyle

var_or_val :: (Monad m, CharParsing m) =>
              PrologParser m v -> PrologParser m (Either String v)
var_or_val v = Left <$> var <|> Right <$> v

atomp :: (Monad m, CharParsing m) =>
         PrologParser m v -> PrologParser m (Atom v (Either String v))
atomp v = do f <- predicate
             args <- optional (parens (commaSep $ var_or_val v))
             return $ atom f (maybe [] id args)
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
            return $ h :- maybe [] id b

program v = some (rule v)
query v   = atomp v

parse p s = case parseString (runPrologParser p) mempty s of
              Success a -> a
              Failure f -> error (show f)

p = parse (program integer) "f(X, Y) :- g(X), h(Y).\
                            \g(1).\
                            \g(2).\
                            \g(3).\
                            \h(3).\
                            \% Some commentary\n\
                            \h(4).\
                            \i(X, Y) :- f(X, Y), not f(Y, X)."

pv = mapM postvaricate p

q = postvaricate $ (parse $ query integer) "i(A, B)"
