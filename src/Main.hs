module Main (main) where

import Grammar.AbsLatte (Program)
import Grammar.ParLatte (myLexer, pProgram)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPrint, hPutStr, hPutStrLn, stderr)
import StaticChecks.TypeChecker (typeCheck)

printFirstErrLine :: Bool -> IO ()
printFirstErrLine True = hPutStr stderr "OK\n"
printFirstErrLine False = hPutStr stderr "ERROR\n"

parseFile :: FilePath -> IO Program
parseFile fileName = do
  fileText <- readFile fileName
  case pProgram (myLexer fileText) of
    Left err -> do
      printFirstErrLine False
      let parsedErr = "SYNTAX ERROR: " ++ err
      hPutStrLn stderr parsedErr
      exitFailure
    Right tree -> do
      pure tree

checkStatic :: Program -> IO ()
checkStatic prog = do
  checkRet <- typeCheck prog
  case checkRet of
    Left err -> do
      printFirstErrLine False
      hPrint stderr err
      exitFailure
    Right warnings -> do
      printFirstErrLine True
      mapM_ (hPrint stderr) warnings

compile :: FilePath -> IO ()
compile fileName = do
  program <- parseFile fileName
  _ <- checkStatic program
  pure ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName] -> compile fileName
    _ -> putStrLn "Usage: ./latc <lat file path>"
