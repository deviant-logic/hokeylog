{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable,
             FlexibleContexts, NoMonomorphismRestriction #-}

module Language.HokeyLog.Syntax where

import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar
import Data.Foldable
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Traversable

data Atom v a = Atom String Int [a]
              | Val v
              deriving (Eq, Ord, Read, Functor, Foldable, Traversable)

atom :: String -> [a] -> Atom v a
atom f args = Atom f (length args) args

instance (Show v, Show a) => Show (Atom v a) where
  show (Atom f _ []) = f
  show (Atom f _ as) = f ++ "(" ++ intercalate ", " (map show as) ++ ")"
  show (Val v)     = show v

data Lit v a = Pos (Atom v a)
             | Neg (Atom v a)
             deriving (Eq, Ord, Read, Functor, Foldable, Traversable)

instance (Show v, Show a) => Show (Lit v a) where
  show (Pos a) = show a
  show (Neg a) = "not " ++ show a

data Rule v a = Atom v a :- [Lit v a]
              deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

pair [] [] = Just []
pair (x:xs) (y:ys) = pair xs ys >>= return . ((x,y):)
pair _ _ = Nothing

instance Eq v => Unifiable (Atom v) where
  zipMatch (Val v) (Val v') | v == v' = Just (Val v)
  zipMatch (Atom f n _) (Atom g m _) | f /= g || n /= m = Nothing
  zipMatch (Atom f n as) (Atom _ _ bs) = return . Atom f n . fmap Right $ zip as bs
  zipMatch _ _ = Nothing

type ATerm x v = UTerm (Atom v) x

varicate :: (Eq v, BindingMonad (Atom v) x m) =>
            Either String v -> StateT (M.Map String x) m (ATerm x v)
varicate (Right v) = return $ UTerm (Val v)
varicate (Left x)  = do mv <- gets (M.lookup x)
                        case mv of
                          Just v -> return $ UVar v
                          Nothing -> do v <- lift freeVar
                                        modify (M.insert x v)
                                        return $ UVar v

postvaricate = flip evalStateT M.empty . traverse varicate

devalue [] = []
devalue (UTerm (Val v):vs) = v : devalue vs
devalue (UTerm t:_) = error "tried to devalue a not-value"
