{-# LANGUAGE OverloadedStrings, BangPatterns #-}

module Main where

import Control.Monad
import Control.Unification
import qualified Data.HashMap.Strict as M
import Data.Monoid
import Language.HokeyLog.Monad
import Language.HokeyLog.Parser as P
import Language.HokeyLog.Program
import Language.HokeyLog.Syntax

import System.Environment
import System.Console.Haskeline
import GHC.Stats

promptStr :: String
promptStr = "?- "

loop :: HM Value (Table Value) -> InputT IO ()
loop db = do minput <- getInputLine promptStr
             case minput of
               Nothing      -> return ()
               Just "quit." -> return ()
               Just input   -> let q = parseQuery value input
                                   as = eval db . ab . (>>= sld . UTerm) $ q in
                               when (null as) (outputStrLn "no.") >> mapM_ (outputStrLn . show) as >> loop db
                               

main :: IO ()
main = do (file:_) <- getArgs
          db <- init_state primops `fmap` parseProgramFile value file
          runInputT defaultSettings $ loop db

primops =[("even" :/: 1, eveng)]
