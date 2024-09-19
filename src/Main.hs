module Main (main) where

import Grammar.AbsLatte (Program)
import Grammar.ParLatte (myLexer, pProgram)
import Grammar.PrintLatte (Print, printTree)
import IrTransformation.NamesChanger (rename)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (replaceExtension)
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
--      printFirstErrLine True
      mapM_ (hPrint stderr) warnings

genCode :: Program -> FilePath -> IO FilePath
genCode prog fileName = do
  let newFileName = replaceExtension fileName ".s"
  genFun prog newFileName
  return newFileName

compile :: FilePath -> IO ()
compile fileName = do
  program <- parseFile fileName
  _ <- checkStatic program
  _ <- genCode program fileName
  pure ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fileName] -> compile fileName
    _ -> putStrLn "Usage: ./latc <lat file path>"

-- under construction

genFun :: Program -> FilePath -> IO ()
genFun program _ = do
  showTree "At the begining" program
  let renamedProgram = rename program
  showTree "With varibales renamed" renamedProgram
  pure ()

showTree :: (Print a) => String -> a -> IO ()
showTree title tree = do
  putStrLn $ "\n[" ++ title ++ "]\n\n" ++ printTree tree
