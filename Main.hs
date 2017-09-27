module Main where

import Data.List (partition)
import System.Environment (getArgs)
import System.IO (hSetBuffering, BufferMode(..), stdout)

import Core
import Simple as S
import Sugar as D

check' e = case check [] e of
             Nothing -> Left "type error"
             Just t  -> Right t

eval' e = return (eval [] e)

goSimple s =
    do e <- parse s
       check' e
       v <- eval' e
       return (show v)
    where parse s = case S.parse s of
                      Left err -> Left (show err)
                      Right e  -> Right e

goData s =
    do e <- parse s
       e' <- desugar e
       check' e'
       v <- eval' e'
       return (show v)
    where parse s = case D.parse s of
                      Left err -> Left (show err)
                      Right e  -> Right e
          desugar e = case D.desugar [] e of
                        Nothing -> Left "desugaring error"
                        Just e  -> Right e


main = do args <- getArgs
          let (options, files) = partition (('-' ==) . head) args
              go | "--core" `elem` options = goSimple
                 | otherwise           = goData
              print (Left err) = putStrLn ("ERROR: " ++ err)
              print (Right v)  = putStrLn v
              repl = do putStr "> "
                        s <- getLine
                        if s == ":q"
                        then return ()
                        else do print (go s)
                                repl

          if null files
          then do hSetBuffering stdout NoBuffering
                  repl
          else mapM_ (\file -> readFile file >>= print . go) files
