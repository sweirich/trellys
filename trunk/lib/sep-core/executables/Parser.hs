module Main where



import Language.SepCore.Happyparser
import System.Environment


main = do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename
      putStrLn $ show $ parser $ lexer cnts
    _ -> putStrLn "usage: sep-core <filename>"
