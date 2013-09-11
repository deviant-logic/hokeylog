{-# LANGUAGE GeneralizedNewtypeDeriving, NoMonomorphismRestriction,
             OverloadedStrings #-}

module Language.HokeyLog.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified Data.HashSet as HS
import Data.Maybe
import Data.Monoid
import Data.String
import Language.HokeyLog.Syntax
import Text.Parser.Token.Highlight
import Text.Parser.Token.Style
import Text.Trifecta
import Text.Trifecta.Result

-- | A parser for prolog-like syntax.
newtype PrologParser m a = PrologParser {
      runPrologParser :: m a
} deriving (Functor, Monad, Applicative, Alternative, CharParsing, Parsing)


-- | Line comments starting with \"%\"
prologCommentStyle :: CommentStyle
prologCommentStyle = CommentStyle "" "" "%" False

-- The identifier styles are spelled out explicitly rather than as
-- record updates of each other so that profiling dumps come out more
-- precisely.  Otherwise, virtually everything gets charged to
-- prologVarStyle.

-- | Alphunmerics or some punctuation (check the source for which so I
-- don't forget to update this comment when I change them).
idbody :: CharParsing m => m Char
idbody = (alphaNum <|> oneOf "-_:")

prologVarStyle, prologAtomStyle, prologPredStyle, prologOpStyle
    :: CharParsing m => IdentifierStyle m
-- | Identifiers with leading uppercase characters.
prologVarStyle =
    IdentifierStyle "prolog variable"
                    upper
                    idbody
                    mempty
                    Identifier
                    ReservedIdentifier

-- | Identifiers with leading lowercase characters, as 'prologPredStyle'.
prologAtomStyle =
    IdentifierStyle "prolog atom"
                    lower
                    idbody
                    mempty
                    Identifier
                    ReservedIdentifier

-- | Identifiers with leading lowercase characters, as 'prologAtomStyle'.
prologPredStyle =
    IdentifierStyle "prolog predicate"
                    lower
                    idbody
                    mempty
                    Identifier
                    ReservedIdentifier

-- | Prolog operators: @:-@, @=@, @not@
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

op :: (Monad m, TokenParsing m) => String -> m ()
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

unification :: (Monad m, IsString s, CharParsing m) =>
              PrologParser m v -> PrologParser m (Atom v (Either s v))
unification v = do a <- var_or_val v
                   op "="
                   b <- var_or_val v
                   return $ atom "=" [a,b]

lit :: (Monad m, IsString s, CharParsing m) =>
      PrologParser m v -> PrologParser m (Lit v (Either s v))
lit v = do m <- optional $ (op "not ")
           a <- atomp v
           return $ case m of
                      Nothing -> Pos a
                      _ -> Neg a

rule :: (Monad m, IsString s, CharParsing m) =>
       PrologParser m v -> PrologParser m (Rule v (Either s v))
rule v = do h <- atomp v
            b <- optional (op ":-" >> commaSep1 (lit v))
            void dot
            return $ h :- fromMaybe [] b

program :: (Monad m, IsString s, CharParsing m) =>
          PrologParser m v -> PrologParser m [Rule v (Either s v)]
program v = some (rule v)

query :: (Monad m, IsString s, CharParsing m) =>
        PrologParser m v -> PrologParser m (Atom v (Either s v))
query v   = atomp v

value :: (Monad m, CharParsing m) => PrologParser m Value
value = Str <$> (predicate <|> fromString <$> stringLiteral)
        <|> Num . fromIntegral <$> integer

parse :: PrologParser Parser a -> String -> a
parse p s = case parseString (runPrologParser p) mempty s of
              Success a -> a
              Failure f -> error (show f)

parseFile :: MonadIO m =>
            PrologParser Parser b -> String -> m b
parseFile p f = do res <- parseFromFile (runPrologParser p) f
                   case res of
                     Just a -> return a
                     Nothing -> error "parse failure"
