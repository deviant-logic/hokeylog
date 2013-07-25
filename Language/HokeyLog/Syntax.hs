{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable,
             FlexibleContexts, NoMonomorphismRestriction,
             OverloadedStrings, MultiParamTypeClasses, TypeSynonymInstances,
             FlexibleInstances #-}

module Language.HokeyLog.Syntax where

import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar
import qualified Data.ByteString.Char8 as B
import Data.Foldable
import Data.Hashable
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Monoid
import Data.Traversable

import Data.Interned
import Data.Interned.ByteString

type ByteString = InternedByteString -- B.ByteString
type PredName = ByteString
type Tuple v = [v]

instance Hashable InternedByteString where
    hashWithSalt s = hashWithSalt s . unintern

data Atom v a = Atom {-# UNPACK #-} !PredName {-# UNPACK #-} !Int (Tuple a)
              | Val v
              deriving (Eq, Ord, Functor, Foldable, Traversable)

atom :: PredName -> [a] -> Atom v a
atom f args = Atom f (length args) args

instance (Show v, Show a) => Show (Atom v a) where
  show (Atom f _ []) = B.unpack . unintern $ f
  show (Atom f _ as) = mconcat [B.unpack . unintern $ f, "(", intercalate ", " (fmap show as), ")"]
  show (Val v)     = show v

data Lit v a = Pos (Atom v a)
             | Neg (Atom v a)
             deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show v, Show a) => Show (Lit v a) where
  show (Pos a) = show a
  show (Neg a) = "not " <> show a

data Rule v a = Atom v a :- [Lit v a]
              deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Eq v => Unifiable (Atom v) where
  zipMatch (Val v) (Val v') | v == v' = Just (Val v)
  zipMatch (Atom f n _) (Atom g m _) | f /= g || n /= m = Nothing
  zipMatch (Atom f n as) (Atom _ _ bs) = return . Atom f n . fmap Right $ zip as bs
  zipMatch _ _ = Nothing

type ATerm v = UTerm (Atom v) IntVar

varicate :: (Eq v, BindingMonad (Atom v) IntVar m) =>
            Either String v -> StateT (M.Map String IntVar) m (ATerm v)
varicate (Right v) = return $ UTerm (Val v)
varicate (Left x)  = do mv <- gets (M.lookup x)
                        case mv of
                          Just v -> return $ UVar v
                          Nothing -> do v <- lift freeVar
                                        modify (M.insert x v)
                                        return $ UVar v

data Value = Str {-# UNPACK #-} !ByteString
           | Num {-# UNPACK #-} !Int
   deriving (Eq, Ord)

instance Show Value where
    show (Str s) = show s
    show (Num i) = show i

postvaricate = flip evalStateT M.empty . traverse varicate

devalue [] = []
devalue (UTerm (Val v):vs) = v : devalue vs
devalue (UTerm t:_) = error "tried to devalue a not-value"
