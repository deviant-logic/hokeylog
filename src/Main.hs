{-# LANGUAGE OverloadedStrings, BangPatterns #-}

module Main where

import Control.Unification
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
               Just input   -> let q = postvaricate . parse (query value) $ input
                                   as = eval db . ab . (>>= sld . UTerm) $ q in
                               mapM_ (outputStrLn . show) as >> loop db
                               

main :: IO ()
main = do (file:_) <- getArgs
          start <- cpuSeconds `fmap` getGCStats
          !w <- parseFile (program value) file
          let l = "some number of records" -- show $ length w
          parse_finished <- cpuSeconds `fmap` getGCStats
          putStrLn $ concat ["loaded ", l, " records in ",
                             show $ parse_finished - start,
                             " seconds"]
          let db = init_table $ mapM postvaricate w
          runInputT defaultSettings $ loop db


