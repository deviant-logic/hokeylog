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

import qualified Data.Vector as V

type ByteString = InternedByteString -- B.ByteString
type PredName = ByteString
type Vector = V.Vector
type Tuple v = Vector v

instance Hashable InternedByteString where
    hashWithSalt s = hashWithSalt s . unintern

data Atom v a = Atom {-# UNPACK #-} !PredName {-# UNPACK #-} !(Tuple a)
              | Val v
              deriving (Eq, Ord, Functor, Foldable, Traversable)

class Atomic t where
    toAtom :: t v a -> Atom v a

instance Atomic Atom where
    toAtom = id

atom :: Foldable t => PredName -> t a -> Atom v a
atom f = Atom f . V.fromList . toList

instance (Show v, Show a) => Show (Atom v a) where
  show (Atom f as) | V.null as = B.unpack . unintern $ f
                   | otherwise = mconcat [B.unpack . unintern $ f,
                                          "(",
                                          intercalate ", " $
                                                      toList (fmap show as),
                                          ")"]
  show (Val v)     = show v

data Lit v a = Pos (Atom v a)
             | Neg (Atom v a)
             deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show v, Show a) => Show (Lit v a) where
  show (Pos a) = show a
  show (Neg a) = "not " <> show a

instance Atomic Lit where
    toAtom (Pos a) = a
    toAtom (Neg a) = a

data Rule v a = Atom v a :- [Lit v a]
              deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Atomic Rule where
    toAtom (a :- _) = a

instance Eq v => Unifiable (Atom v) where
  zipMatch (Val v) (Val v') | v == v' = Just (Val v)
  zipMatch (Atom f as) (Atom g bs) | V.length as /= V.length bs || f /= g = Nothing
  zipMatch (Atom f as) (Atom _ bs) = return . Atom f . fmap Right $ V.zip as bs
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

devalue :: Functor f => f (ATerm v) -> f v
devalue = fmap devalue'
    where devalue' (UTerm (Val v)) = v
          devalue' _ = error "tried to devalue a not-value"
