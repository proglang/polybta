{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
import Development.Shake hiding ((*>))
import Development.Shake.FilePath
import Control.Applicative
import Data.Maybe
import Data.Monoid
import Control.Exception
import Control.Monad
import qualified Data.List as List
import qualified Text.Regex.Applicative as Re
import qualified System.IO as Sys
import qualified System.Directory as Sys
import qualified System.Environment as Sys
import qualified Data.Char as Char
import qualified Data.ByteString as BS
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Options.Applicative as Opt

import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
       
       
import Debug.Trace

type Module = String
     
data PlanArgs = PlanArgs { pArg_ignored :: [Module]
                         , pArg_agdaArgs :: [String]
                         , pArg_sources :: [FilePath]
                         , pArg_root :: FilePath
                         }

plan :: PlanArgs -> Rules ()
plan PlanArgs{..} = do
  let modules = map sourceToModule pArg_sources
  want (wantedTargets modules)
  "_build/*.want" %> \out -> do
     let sourceDir = takeDirectory out </> ".."
         source = sourceDir </> takeFileName out -<.> "agda"              
     need [source]
     listedDeps <- liftIO $ getDepModules source
     let deps = wantedTargets listedDeps
     need deps
     let buildDir = "_build"
     command_ [Cwd buildDir] "agda" (pArg_agdaArgs 
                                    ++[fromJust (List.stripPrefix "_build/" source)])
     liftIO $ writeFile out ""
     return ()
  where wantedTargets ms = [moduleToTarget m | m <- ms, (not (m `elem` pArg_ignored))]
  
-- TODO: find a way to read those from the actual stdlib dir
manualAgdaLibs :: [Module]
manualAgdaLibs = 
  [ "Data.Bool"
  , "Data.Unit"
  , "Category.Functor"
  , "Relation.Binary.PropositionalEquality"
  , "Relation.Nullary"
  , "Relation.Binary"
  , "Data.Empty"
  , "Data.Sum"
  , "Data.Product"
  , "Data.List"
  , "Data.Nat"
  , "Function"
  , "Data.Nat.Properties"
  , "Algebra.FunctionProperties"
  , "Data.Fin"
  , "Level"
  , "Category.Monad"
  , "Data.Maybe"
  , "Relation.Nullary.Decidable"
  , "Data.Vec"
  ]
  
data Opt = Opt { optSources :: [FilePath]
               , optIncludes :: [FilePath]
               }
  deriving Show

getOpt :: IO Opt
getOpt = Opt.execParser (Opt.info (Opt.helper <*> parseOpt) 
                                  (Opt.fullDesc
                                  <> Opt.progDesc "Build Agda sources with dependencies."))
  where parseOpt :: Opt.Parser Opt
        parseOpt = Opt 
                 <$> many (Opt.strArgument (Opt.help "Source file" 
                                           <> Opt.metavar "FILE"))
                 <*> many (Opt.strOption (Opt.short 'i' 
                             <> Opt.help "add directory to library path"
                             <> Opt.metavar "DIR"))
                 
  
main :: IO ()
main = do
  opt@Opt{..} <- getOpt
  failingModules <- parseFailingModules <$> Sys.readFile "failing-modules.txt"
  -- TODO: do not hard-code --allow-unsolved-metas
  here <- Sys.getCurrentDirectory
  let mkAbsolute p = if (isRelative p) then here </> p else p
  let pArg_agdaArgs = concat [["-i", mkAbsolute i] | i <- optIncludes] ++ ["--allow-unsolved-metas"]
      pArg_sources = map takeFileName optSources
      pArg_ignored = manualAgdaLibs ++ failingModules
      pArg_root = "."
  shake shakeOptions (plan PlanArgs{..})
  reportFailing failingModules
  
reportFailing :: [Module] -> IO ()
reportFailing ms = do
  putStrLn "These modules are ignored:"
  forM_ ms $ \m -> do
    putStr "  * " 
    putStrLn m

  
-- TODO: do I want these?
getSources :: IO [FilePath]
getSources = filter (".agda" `List.isSuffixOf`) <$> Sys.getDirectoryContents "."
getLib :: IO [FilePath]
getLib = undefined


parseFailingModules :: String -> [Module]
parseFailingModules file = filter (not . ignored) (map trim (lines file))
  where trim = reverse . dropWhile Char.isSpace . reverse . dropWhile Char.isSpace
        ignored s = null s || "#" `List.isPrefixOf` s
     
           
getDepModules :: FilePath -> IO [Module]
getDepModules f = do
  contents <- readUtf8File f
  return $ parseImports contents
  
parseImports :: String -> [Module]
parseImports = catMaybes . map (Re.match p_import) . lines
  where p_import = spaces *> optional ("open " *> spaces) 
                   *> "import " *> spaces *> parseIdent <* Re.many Re.anySym
        spaces = Re.few (Re.psym (Char.isSpace))

parseIdent :: Re.RE Char String
parseIdent = many (Re.psym (\c -> not (c `elem` "()") 
                                  && not (Char.isSpace c)))
           
readUtf8File :: FilePath -> IO String
readUtf8File f = Text.unpack . Text.decodeUtf8  <$> BS.readFile f
     
              
moduleToTarget :: String -> FilePath
moduleToTarget m = "_build" </> replace '.' '/' m <.> "want"
sourceToModule :: FilePath -> String
sourceToModule src = assert (isRelative src) $ replace '/' '.' (dropExtension src)
replace :: Char -> Char -> String -> String
replace old new s = map (\c -> if c == old then new else c) s
        
tests = testGroup "Tests" [
          testGroup "Conversions" [
            testCase "src -> module" $
              sourceToModule "M1/A.agda" @?= "M1.A"
          , testCase "module -> target" $
              moduleToTarget "M1.A" @?= "_build/M1/A.want"       
          , testCase "src -> module (toplevel)" $
              sourceToModule "Abc.agda" @?= "Abc"
          , testCase "module -> target" $
              moduleToTarget "Abc" @?= "_build/Abc.want"
          ]
        , testGroup "Import parser" [
            testCase "simple import (one line)" $
              parseImports "import Data.Char" @?= ["Data.Char"]
          , testCase "import with tail (one line)" $
              parseImports "import Data.Char(abs,def)" @?= ["Data.Char"]
          , testCase "import with space and tail (one line)" $
              parseImports "import Data.Char   (abs,def)" @?= ["Data.Char"]
          , testCase "several imports (with open)" $
              parseImports ("import Data.Char  \n\  
                            \  open import Data.Num (abs,def) hiding xxx\n\
                            \ import Category.Monad (join, (>>=))") 
              @?= ["Data.Char", "Data.Num", "Category.Monad"]
          , testCase "imports interleaved with stuff" $
              parseImports ("module HelloWorld where\n\
                           \ import Data.Char\n\n\n\
                           \ IamTestingSomething\n\
                           \ module Sub1 where\n\
                           \   open import Category.Monad\n\n\
                           \ againTesting")
              @?= ["Data.Char", "Category.Monad"]
          ]
        , testGroup "Failing modules" $ [
             testCase "ignore empty" $
               parseFailingModules "" @?= []
          ,  testCase "ignore empties" $
               parseFailingModules "\n  \n\n" @?= []
          , testCase "parse 1" $
               parseFailingModules "Data.Char" @?= ["Data.Char"]
          , testCase "ignore comment" $
               parseFailingModules "#Hello World" @?= []
          , testCase "ignore comments and empties" $
               parseFailingModules "  #Hello World\n\
                                   \   \n\n\
                                   \# What is up!...\n" @?= []
          , testCase "example ignore file" $ 
               parseFailingModules "\
                \# List of modules that are expected to fail, one per line\n\
                \PE-STLCFix\n\
                \PHOAS2DB-Correctness\n" @?= (["PE-STLCFix", "PHOAS2DB-Correctness"] :: [Module])
          ]
        ]
