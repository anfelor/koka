import Control.Monad
import Control.Monad.IO.Class
import Control.Exception (bracket)
import Data.Maybe
import Data.Char
import Data.List
import Data.List.Extra (replace, trim)
import Data.Time.Clock (addUTCTime)
import System.Directory
import System.Environment
import System.Exit (ExitCode(..))
import System.FilePath
import System.IO
import qualified System.Info as Sys
import System.Process (readProcessWithExitCode)
import Text.Regex
import Text.JSON
import Test.Hspec
import Test.Hspec.Core.Runner
import Test.Hspec.Core.Formatters hiding (Error)
import qualified NameSpec(spec)
import qualified Data.Map as M
import qualified Common.Name as N
import qualified Common.NamePrim as NP
import qualified Backend.Typed.Syntax as T
import qualified Backend.Typed.Types as TT
import qualified Backend.Typed.Query as TQ
import qualified Backend.Typed.Check as TC
import qualified Backend.Typed.Linear as TL
import qualified Backend.Typed.Passes.Anf as TA
import qualified Backend.Typed.Passes.Contify as TF
import qualified Backend.Typed.Passes.Perceus as TP
import qualified Backend.Typed.Passes.Reuse as TR
import qualified Backend.Typed.Passes.Match as TM
import qualified Backend.Typed.CGen as CG
import Kind.Newtypes (newtypesEmpty)


commonFlags :: [String]
commonFlags = ["-c", "-v0", "--console=raw",
               "-O1", -- for cgen/specialize
               -- "--cc=clang",
               -- "--checkcore",
               "-itest",  -- "-ilib",
               "--buildtag=test", "--no-buildhash"]

data Mode = Test | New | Update
  deriving (Eq, Ord, Show)


-- the C backend, or the typed backend (`--typedc`, executing the typed executable)
data Backend = BackendC | BackendTyped
  deriving (Eq, Ord, Show)

data Options = Options{ mode :: Mode, cabal :: Bool, sysghc:: Bool, opt :: Int, target :: String, par :: Bool, rebuild :: Bool, backends :: [Backend] }

optionsDefault = Options Test False False 0 "" True False [BackendC]

data Cfg = Cfg{ flags   :: [String],
                options :: Options,
                exclude :: [String],
                fexclude:: !(String -> Bool)
              }

makeCfg :: [String] -> Options -> [String] -> Cfg
makeCfg flags options []
  = Cfg flags options [] (\s -> False)
makeCfg flags options exclude
  = Cfg flags options exclude fexclude
  where
    matcher item | any (\c -> c `elem` "()[]+*?") item = let r = mkRegex item
                                                         in (\s -> isJust (matchRegex r s))
                 | otherwise = (\s -> s == item || s == (item ++ ".kk"))
    matchers   = map matcher exclude
    fexclude s = any (\m -> m s) matchers

normalizePlatformKey :: String -> String
normalizePlatformKey = map norm
  where
    norm c | c == '_' = '-'
           | otherwise = toLower c

instance JSON Cfg where
  showJSON cfg = JSObject (toJSObject [])
  readJSON val
    = case val of
        JSObject obj
          -> let flags = case valFromObj "flags" obj of
                           Ok s -> words s
                           _    -> []
                 exclude = case valFromObj "exclude" obj of
                             Ok xs -> xs
                             _     -> []
                 pexclude = case valFromObj "exclude-platform" obj of
                              Ok v -> platformExcludes v
                              _    -> []
                 platformExcludes v
                   = case v of
                       JSObject pobj -> concatMap matchPlatform (fromJSObject pobj)
                       _             -> []
                 matchPlatform (platform, excludes)
                   | normalizePlatformKey platform `elem` platformKeys
                   = case excludes of
                       JSArray xs -> mapMaybe toString xs
                       _          -> []
                   | otherwise
                   = []
                 toString (JSString s) = Just (fromJSString s)
                 toString _            = Nothing
                 platformKeys = [os, arch, os ++ "-" ++ arch]
                 -- see also src/Compile/Option.hs
                 os   = case normalizePlatformKey Sys.os of
                          "darwin"  -> "macos"
                          "mingw32" -> "windows"
                          o         -> o
                 arch = case normalizePlatformKey Sys.arch of
                          "aarch64" -> "arm64"
                          "armv8"   -> "arm64"
                          "armv9"   -> "arm64"
                          "x86-64"  -> "x64"
                          "x86_64"  -> "x64"
                          "amd64"   -> "x64"
                          a          -> a
               in Ok (makeCfg flags optionsDefault (exclude ++ pexclude))
        JSNull     -> Ok (makeCfg [] optionsDefault [])
        JSString s -> Ok (makeCfg (words (fromJSString s)) optionsDefault [])
        _          -> Error ("invalid JSON object")

extendCfg :: Cfg -> Cfg -> Cfg
extendCfg (Cfg flags1 opts1 exclude1 fexclude1) (Cfg flags2 opts2 exclude2 fexclude2)
  = Cfg (flags1 ++ flags2) opts1
        (exclude1 ++ exclude2) (\s -> fexclude1 s || fexclude2 s)

initialCfg :: Options -> Backend -> Cfg
initialCfg options backend
  = makeCfg (commonFlags ++ backendFlags ++ if (not (null (target options))) then ["--target=" ++ target options] else [])
            options []
  where
    -- the typed backend needs its own build directory as it generates extra C for every module
    backendFlags = case backend of
                     BackendC     -> []
                     BackendTyped -> ["--typedc", "--buildtag=test-typed"]


readFlagsFile :: FilePath -> IO [String]
readFlagsFile fp
  = do exists <- doesFileExist fp
       if not exists
         then return []
         else words <$> readFile fp

testSanitize :: FilePath -> String -> String
testSanitize kokaDir
  = trim
  . sub "^compile *:.*kklib.*\n" ""
  . sub "^Up to date\n" ""
  . sub "\n[[:space:]]+at .*" ""
  . sub "(std_core\\.js:)[[:digit:]]+" "\\1"
  . sub "[\r\n]+" "\n"
  . sub "[[:blank:]]+" " "
  . sub "\\\\" "/"
   -- type variable names and box names
  . sub "\\@box-x[[:digit:]]+(-x[[:digit:]]+)?" "@box-xxx"
  . sub "(\\@[a-zA-Z])[[:digit:]]+" "\\1xxx"
  . sub "([a-zA-Z])@[[:digit:]@]+" "\\1@xxx"
  . sub "([a-zA-Z])\\.[[:digit:]]+\\.[[:digit:]]+" "\\1@xxx"
  . sub "<[[:digit:]]+>" "<0>"
  -- for tests using --showhiddentypesigs,
  -- @unroll-xxx
  -- e.g. .lift250-main => .lift000-main
  --      f: (z00.192 : a) -> a => f: (a.00.000 : a) -> a
  . sub "([[:alpha:]][[:alpha:]]+)[[:digit:]][[:digit:]][[:digit:]]+" "\\1xxx"  -- xs254 ~> xsxxx
  . sub "@unroll-[[:alnum:]@-]+" "@unroll-xxx"                   -- @unroll-main12 ~> @unroll-xxx
  . sub "(@m?)lift-[[:alnum:]@-]+" "\\1lift-xxx"                 -- @mlift-main33  ~> @mlift-xxx
  . sub "(^[[:alnum:]]+\\/.+:.*) [[:alpha:]]+[[:digit:]]+@[[:digit:]]+ :" "\\1 a00.000 :"
  -- . sub ": [[:digit:]]+([,\\)])" ": 0\\1"
  -- old style handlers
  . sub "@hnd-" ""
  -- using @ for hidden names now
  . sub "\\." "@"
  -- standard qualifiers
  . sub "(console|hnd|sslice|string|list)/" ""
 . if null kokaDir then id else replace xkokaDir "..."
  where
    xkokaDir = case map (\c -> if c == '\\' then '/' else c) kokaDir of
                 (c:':':rest) -> [toLower c] ++ ":" ++ rest
                 path -> path

    sub re = flip (subRegex (mkRegex re))
    -- limitTo n s | length s > n = take n s ++ "... (and more)"
    --             | otherwise    = s

expectedSanitize :: String -> String
expectedSanitize input
  = filter (/='\r') input   -- on windows \r still gets through sometimes

runKoka :: Cfg -> FilePath -> FilePath -> IO String
runKoka cfg kokaDir fp
  = do caseFlags <- readFlagsFile (fp ++ ".flags")
       let relTest = makeRelative kokaDir fp
           optFlag   = if (opt (options cfg) /= 0) then ["-O" ++ show (opt (options cfg))] else []
           kokaFlags = optFlag ++ flags cfg ++ caseFlags           
       if (cabal (options cfg))
         then do let argv = ["new-run", "koka", "--"] ++ kokaFlags ++ [relTest]
                 (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" argv ""
                 return (testSanitize kokaDir stdout)
         else do let stackFlags = if (sysghc (options cfg)) then ["--system-ghc","--skip-ghc-check"] else []
                     argv = ["exec","koka"] ++ stackFlags ++ ["--"] ++ kokaFlags ++ [relTest]
                 -- hPutStrLn stderr (unwords argv) -- show koka command
                 (exitCode, stdout, stderr) <- readProcessWithExitCode "stack" argv ""
                 -- putStrLn stdout
                 return (testSanitize kokaDir stdout)



makeTest :: Cfg -> FilePath -> Spec
makeTest cfg fp
  | takeExtension fp == ".kk"
      = do let expectedFile = fp ++ ".out"
           isTest <- runIO $ doesFileExist expectedFile
           let shouldRun = not isTest && mode (options cfg) == New || isTest && mode (options cfg) /= New
           when shouldRun $
             it (takeBaseName fp) $ do
               kokaDir <- getCurrentDirectory
               out <- runKoka cfg kokaDir fp
               unless (mode (options cfg) == Test) $ (withBinaryFile expectedFile WriteMode (\h -> hPutStr h out)) -- writeFile expectedFile out
               expected <- testSanitize kokaDir <$> readFile expectedFile
               out `shouldBe` expected
  | otherwise
      = return ()

discoverTests :: Cfg -> FilePath -> Spec
discoverTests cfg0 p = discover cfg0 "" p
  where discover cfg cat p
          = do isDirectory <- runIO $ doesDirectoryExist p
               if not isDirectory
                 then makeTest cfg p
                 else do
                   fs0  <- runIO (sort <$> listDirectory p)
                   cfg' <- runIO (readConfigFile cfg p)
                   let fs   = filter (not . fexclude cfg') fs0  -- todo: make ignoring the failing optional
                       with = if cat == "" then id else describe cat
                   with $ mapM_ (\f -> discover cfg' f (p </> f)) fs

readConfigFile :: Cfg -> FilePath -> IO Cfg
readConfigFile cfg dir
  = do let fname = dir </> "config.json"
       hasCfg <- doesFileExist fname
       if (not hasCfg) then return cfg
         else do txt <- readFile fname
                 case decode (trim (removeLineComments txt)) of
                   Ok cfg'   -> return (extendCfg cfg cfg')
                   Error err -> do putStrLn ("(warning: " ++ fname ++ ": " ++ err ++ ")")
                                   return cfg
  where
    -- allow limited form of line comments that cannot contain " or / characters
    removeLineComments txt
      = unlines (map removeLineComment (lines txt))
    removeLineComment cs
      = case dropWhile (\c -> not (c `elem` "/\"")) (reverse cs) of
          ('/':'/':rev) -> reverse rev
          _             -> cs




processOptions :: String -> (Options, [String]) -> (Options,[String])
processOptions arg (options,hargs)
  = if (take 7 arg == "--mode=")
      then let m = parseMode (drop 7 arg)
           in (options{ mode = m }, hargs)
    else if (arg == "--cabal")
      then (options{cabal=True}, hargs)
    else if (take 2 arg == "-O")
      then (options{opt=read (drop 2 arg)}, hargs)
    else if (arg == "--system-ghc")
      then (options{sysghc=True}, hargs)
    else if (arg == "--target-js")
      then (options{target="js"}, hargs)
    else if (arg == "--target-c64c")
      then (options{target="c64c"}, hargs)
    else if (arg == "--names")
      then (options{target="names"}, hargs)
    else if (arg == "--seq")
      then (options{par=False}, hargs)
    else if (arg == "--rebuild" || arg == "-r")
      then (options{rebuild=True}, hargs)
    else if (take 10 arg == "--backend=")
      then (options{backends=parseBackend (drop 10 arg)}, hargs)
      else (options, arg : hargs)
  where
    parseMode :: String -> Mode
    parseMode "new" = New
    parseMode "update" = Update
    parseMode "test" = Test
    parseMode m = error $ "Unrecognized mode: " ++ show m

    parseBackend :: String -> [Backend]
    parseBackend "c" = [BackendC]
    parseBackend "typed" = [BackendTyped]
    parseBackend "both" = [BackendC,BackendTyped]
    parseBackend b = error $ "Unrecognized backend: " ++ show b

getOptions :: IO (Options , [String])
getOptions
  = do argv <- getArgs
       return (foldr processOptions (optionsDefault,[]) argv)

main :: IO ()
main = do
  setEnv "LC_ALL" "C"  -- for unicode
  pwd <- getCurrentDirectory
  (options0, args) <- getOptions
  cabalEnv <- do stackExe <- lookupEnv "STACK_EXE"
                 return (maybe "" id stackExe == "")
  let options = options0{ cabal = cabalEnv || cabal options0 }
  hcfg <- readConfig defaultConfig args
  -- the typed backend only generates native C; new and updated expected output come from the C backend
  let runBackends = if (null (target options) && mode options == Test) then backends options else filter (/= BackendTyped) (backends options)
  putStrLn "pre-compiling standard libraries..."
  precompiled <- mapM (precompile options) runBackends
  putStrLn "ok."
  let spec = if target options == "names"
               then NameSpec.spec
               else (if (target options == "js" || not (par options)) then id else parallel) $
                    mapM_ (\(backend,out) -> withBackend backend $
                                              do when (backend == BackendTyped) $
                                                   do typedStdTest out
                                                      typedIRTest
                                                      typedPassTest
                                                      typedBuildTest options
                                                 discoverTests (initialCfg options backend) (pwd </> "test"))
                          (zip runBackends precompiled)
      withBackend backend = if (length runBackends > 1) then describe (backendName backend) else id
  summary <- withArgs [] (runSpec spec hcfg{configFormatter=Just specProgress})
  evaluateSummary summary

backendName :: Backend -> String
backendName BackendC     = "c"
backendName BackendTyped = "typed"

-- the typed backend reports problems in the precompiled modules (not in the tests) only once,
-- when they are compiled (use `--rebuild` to check them again)
typedStdTest :: String -> Spec
typedStdTest out
  = it "std" $ filter ("typed " `isPrefixOf`) (lines out) `shouldBe` []

-- Credits are linear unboxed values; boxed duplicates must preserve their original sum tag.
typedIRTest :: Spec
typedIRTest = describe "typed IR ownership" $ do
  let sumA = T.ASum . TT.sumAlts
      n = N.newName
      r = n "r"
      q = n "q"
      j = n "j"
      credit = T.VReuse 16 Nothing
      env = TQ.Env M.empty M.empty
      gamma = M.singleton r (T.V credit)
      program args result body = T.Program (n "typed-ir") M.empty M.empty
        [T.DefFun (n "test") [] args result body]
      transfer = program [(r,T.Owned,credit)] credit
        (T.Join j [(q,T.Owned,credit)] (T.Ret (T.Var q)) (T.Jump j [T.Var r]))
  it "transfers credits through returns and joins" $ do
    TC.checkProgram transfer `shouldBe` []
    TL.checkLinear transfer `shouldBe` []
  it "frees credits and rejects dropping them as boxed operands" $ do
    let prog = program [(r,T.Owned,credit)] T.VUnit (T.Free r (T.Ret T.UnitV))
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    TQ.inferE env gamma M.empty (T.Drop r (T.Ret T.UnitV)) `shouldSatisfy` isLeft
  it "rejects duplication of credits and aggregates containing credits" $ do
    TQ.inferV env gamma (T.DupV (T.Var r)) `shouldSatisfy` isLeft
    TQ.inferV env gamma (T.DupV (T.Pair T.UnitV (T.Var r))) `shouldSatisfy` isLeft
  it "rejects an unconsumed credit" $
    TL.checkLinear (program [(r,T.Owned,credit)] T.VUnit (T.Ret T.UnitV)) `shouldSatisfy` (not . null)
  it "rejects credits in heap payloads and closure captures" $ do
    TQ.inferA env gamma (T.Box (T.Var r)) `shouldSatisfy` isLeft
    TQ.inferA env gamma (T.Lam [] T.VUnit (T.Free r (T.Ret T.UnitV))) `shouldSatisfy` isLeft
  it "records reuse contents without borrowing or owning the payload twice" $ do
    let arg = n "arg"
        z = n "box"
        x = n "payload"
        payload = T.VPtr T.AUnit
        result = T.VPtr (T.ABox payload)
        described = T.VReuse 16 (Just (T.Var x))
        body = T.Deref T.Unique (T.Var arg) z
          (T.UnboxRu z x r (T.Let q described (T.Ret (T.Var r))
            (T.Ret (T.Ptr (T.ABox payload) (T.BoxAt q (T.Var x))))))
        prog = program [(arg,T.Unique,result)] result body
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
  it "refines reuse contents when the payload is destructured" $ do
    let z = n "box"
        x = n "payload"
        a = n "a"
        b = n "b"
        payload = T.VProd (T.VPtr T.AUnit) (T.VPtr T.AUnit)
        described = T.VReuse 24 (Just (T.Pair (T.Var a) (T.Var b)))
        ctx = M.singleton z (T.A (T.ABox payload))
        body = T.UnboxRu z x r (T.Unpair T.Owned (T.Var x) a b
          (T.Let q described (T.Ret (T.Var r)) (T.Ret (T.Var q))))
    TQ.inferE env ctx M.empty body `shouldBe` Right (T.VReuse 24 Nothing)
  it "forgets local reuse descriptions and rejects fabricated identities" $ do
    let z = n "box"
        x = n "payload"
        y = n "other"
        payload = T.VPtr T.AUnit
        ctx = M.fromList [(z,T.A (T.ABox payload)),(y,T.V payload)]
        extract = T.UnboxRu z x r (T.Ret (T.Var r))
        forged = T.UnboxRu z x r
          (T.Let q (T.VReuse 16 (Just (T.Var y))) (T.Ret (T.Var r)) (T.Ret (T.Var q)))
    TQ.inferE env ctx M.empty extract `shouldBe` Right credit
    TQ.inferE env ctx M.empty forged `shouldSatisfy` isLeft
    TQ.inferE env ctx M.empty
      (T.UnboxRu z x r (T.Let x payload (T.Ret (T.Var y)) (T.Ret (T.Var r)))) `shouldSatisfy` isLeft
    TQ.inferE env ctx M.empty
      (T.Let q (T.VReuse 16 (Just (T.Var x))) extract (T.Ret (T.Var q))) `shouldSatisfy` isLeft
  it "checks description structure and size, and allows empty described credits" $ do
    let x = n "payload"
        ctx = M.singleton x (T.V (T.VPtr T.AUnit))
        check t = TQ.checkE env ctx M.empty (T.Ret (T.NoReuse 16)) t
    check (T.VReuse 16 (Just (T.Var x))) `shouldBe` Right ()
    forM_ [T.VReuse 24 (Just (T.Var x)),
           T.VReuse 16 (Just (T.DupV (T.Var x))),
           T.VReuse 16 (Just (T.Ptr (T.ABox (T.VPtr T.AUnit)) (T.Box (T.Var x))))] $ \t ->
      check t `shouldSatisfy` isLeft
  it "rejects opaque alternatives in boxed sums" $ do
    let a = sumA [T.AUnit, T.AFun [] T.VUnit]
    TQ.inferA env M.empty (T.InjA 1 a (T.Lam [] T.VUnit (T.Ret T.UnitV))) `shouldSatisfy` isLeft
  it "preserves the tag offset when duplicating an operand of a sub-sum" $ do
    let arg = n "arg"
        x = n "x"
        l = n "left"
        y = n "subsum"
        z = n "duplicate"
        a = n "a"
        b = n "b"
        box = T.ABox (T.VPtr T.AUnit)
        sumType = sumA [T.AUnit, sumA [box,box]]
        done = T.Ret T.UnitV
        body = T.Deref T.Owned (T.Var arg) x
          (T.CaseA T.Owned x [(0,l,done),
            (1,y,T.Dup y z (T.Drop y
              (T.CaseA T.Owned z [(0,a,T.Drop a done),(1,b,T.Drop b done)] Nothing)))] Nothing)
        prog = program [(arg,T.Owned,T.VPtr sumType)] T.VUnit body
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    -- Both the outer sum and the duplicated sub-sum use tags 2 and 3.
    [ws | line <- lines source, let ws = words line, take 1 ws == ["case"]]
      `shouldBe` [["case","1:"],["case","2:"],["case","3:"],["case","2:"],["case","3:"]]
  it "specializes reuse stores after payload destructuring and credit aliasing" $ do
    let arg = n "arg"
        z = n "box"
        p = n "payload"
        a = n "a"
        b = n "b"
        value = T.Pair (T.Var a) (T.Lit (T.LitChar 'x'))
        -- Use a raw char field so its replacement is a literal of the same type.
        charPayload = T.VProd (T.VPtr T.AUnit) (T.VRaw NP.nameTpChar)
        charResult = T.VPtr (T.ABox charPayload)
        body = T.Deref T.Unique (T.Var arg) z
          (T.UnboxRu z p r (T.Unpair T.Owned (T.Var p) a b
            (T.Let q (T.VReuse 24 Nothing) (T.Ret (T.Var r))
              (T.Free q (T.Ret (T.Ptr (T.ABox charPayload) (T.Box value)))))))
        (prog,errs) = TR.reuseProgram (program [(arg,T.Unique,charResult)] charResult body)
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    errs `shouldBe` []
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    source `shouldSatisfy` isInfixOf "reuse_payload"
    source `shouldSatisfy` isInfixOf "->p.f1 ="
    source `shouldSatisfy` (not . isInfixOf "->p.f0 =")
    source `shouldSatisfy` isInfixOf "} else {"
  it "keeps dup effects when matching field stores are omitted" $ do
    let arg = n "arg"
        z = n "box"
        p = n "payload"
        a = n "a"
        b = n "b"
        field = T.VPtr T.AUnit
        payload = T.VProd field field
        box = T.VPtr (T.ABox payload)
        result = T.VProd box field
        body = T.Deref T.Unique (T.Var arg) z
          (T.UnboxRu z p r (T.Unpair T.Owned (T.Var p) a b
            (T.Ret (T.Pair (T.Ptr (T.ABox payload)
              (T.BoxAt r (T.Pair (T.DupV (T.Var a)) (T.Var b)))) (T.Var a)))))
        prog = program [(arg,T.Unique,box)] result body
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    source `shouldSatisfy` isInfixOf "kk_box_dup"
    source `shouldSatisfy` isInfixOf "reuse_payload"
    source `shouldSatisfy` (not . isInfixOf "->p.f0 =")
    source `shouldSatisfy` (not . isInfixOf "->p.f1 =")
  it "specializes credits through sums and existential payloads" $ do
    let arg = n "arg"
        z = n "box"
        p = n "payload"
        x = n "x"
        a = n "a"
        b = n "b"
        field = T.VPtr T.AUnit
        sumPayload = T.VSum [T.VProd field field,T.VUnit]
        existsPayload = T.VExists [0] (T.VProd (T.VPtr (T.AVar 0)) (T.VRaw NP.nameTpChar))
        rebuild payload value = T.Ret (T.Ptr (T.ABox payload) (T.BoxAt r value))
        sumBody = T.CaseV T.Owned (T.Var p)
          [(x,rebuild sumPayload (T.Inj 0 sumPayload (T.Var x))),
           (x,rebuild sumPayload (T.Inj 1 sumPayload (T.Var x)))]
        existsBody = T.Unpack T.Owned (T.Var p) [1] x
          (T.Unpair T.Owned (T.Var x) a b
            (rebuild existsPayload (T.Pack existsPayload [T.AVar 1] (T.Pair (T.Var a) (T.Var b)))))
    forM_ [(sumPayload,sumBody),(existsPayload,existsBody)] $ \(payload,e) -> do
      let result = T.VPtr (T.ABox payload)
          prog = program [(arg,T.Unique,result)] result
            (T.Deref T.Unique (T.Var arg) z (T.UnboxRu z p r e))
          cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
          (_,source,errors) = CG.cgenModule cenv prog
      TC.checkProgram prog `shouldBe` []
      TL.checkLinear prog `shouldBe` []
      errors `shouldBe` []
      source `shouldSatisfy` isInfixOf "reuse_payload"
  it "equates a duplicate alias with the original payload" $ do
    let arg = n "arg"
        z = n "box"
        p = n "payload"
        y = n "duplicate"
        payload = T.VPtr T.AUnit
        result = T.VPtr (T.ABox payload)
        body = T.Deref T.Unique (T.Var arg) z
          (T.UnboxRu z p r (T.Let y payload (T.Ret (T.DupV (T.Var p)))
            (T.Deref T.Owned (T.Var p) q (T.Drop q
              (T.Ret (T.Ptr (T.ABox payload) (T.BoxAt r (T.Var y))))))))
        -- A duplicate keeps the payload's bits, so the store is omitted (the dup still runs).
        prog = program [(arg,T.Unique,result)] result body
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    source `shouldSatisfy` isInfixOf "reuse_payload"
  it "checks boxed injection indices and sparse case coverage" $ do
    let sumType = sumA [T.AUnit,T.AUnit,T.AUnit]
        x = n "sum"
        y = n "alternative"
        d = n "default"
        done = T.Ret T.UnitV
        ctx = M.singleton x (T.A sumType)
        infer e = TQ.inferE env ctx M.empty e
    forM_ [-1,3] $ \i ->
      TQ.inferA env M.empty (T.InjA i sumType T.UnitA) `shouldSatisfy` isLeft
    TQ.inferA env M.empty (T.InjA 2 sumType T.UnitA) `shouldBe` Right sumType
    infer (T.CaseA T.Owned x [(2,y,done)] (Just (d,done))) `shouldBe` Right T.VUnit
    forM_ [T.CaseA T.Owned x [(2,y,done)] Nothing,
           T.CaseA T.Owned x [(2,y,done),(2,d,done)] (Just (d,done)),
           T.CaseA T.Owned x [(3,y,done)] (Just (d,done))] $ \e ->
      infer e `shouldSatisfy` isLeft
  it "keeps one default and consumes its residual sum through Perceus" $ do
    let arg = n "arg"
        x = n "sum"
        y = n "alternative"
        d = n "default"
        sumType = sumA (replicate 4 (T.ABox (T.VPtr T.AUnit)))
        body = T.Deref T.Owned (T.Var arg) x
          (T.CaseA T.Owned x [(2,y,T.Ret T.UnitV)] (Just (d,T.Ret T.UnitV)))
        input = program [(arg,T.Owned,T.VPtr sumType)] T.VUnit body
        (prog,errs) = TP.perceusProgram input
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    errs `shouldBe` []
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    source `shouldSatisfy` isInfixOf "== 3"
    source `shouldNotSatisfy` isInfixOf "== 1"
    source `shouldNotSatisfy` isInfixOf "== 2"
    source `shouldNotSatisfy` isInfixOf "== 4"
  it "narrows defaults without renumbering constructor indices" $ do
    let x = n "sum"
        y = n "alternative"
        d = n "default"
        box = T.ABox (T.VPtr T.AUnit)
        sumType = T.ASum [(0,box),(2,box),(5,box)]
        rest = T.ASum [(0,box),(5,box)]
        done = T.Ret T.UnitV
        expr = T.CaseA T.Owned x [(2,y,T.Drop y done)] (Just (d,T.Drop d done))
        ctx = M.singleton x (T.A sumType)
    TQ.altTypes env (T.A sumType) expr `shouldBe` Right [[T.A box],[T.A rest]]
    TQ.inferE env ctx M.empty expr `shouldBe` Right T.VUnit
    TQ.inferE env (M.singleton d (T.A rest)) M.empty
      (T.CaseA T.Owned d [(2,y,done)] (Just (x,done))) `shouldSatisfy` isLeft
    TQ.inferA env M.empty (T.InjA 2 rest (T.Box T.UnitV)) `shouldSatisfy` isLeft
    TQ.altTypes env (T.A sumType)
      (T.CaseA T.Owned x [(i,y,done) | i <- [0,2,5]] (Just (d,done))) `shouldSatisfy` isLeft
    forM_ [T.ASum [(0,box),(0,box)], T.ASum [(2,box),(0,box)],
           T.ASum [(-1,box)], T.ASum [(0,sumA [box,box]),(1,box)]] $ \bad ->
      TQ.altTypes env (T.A bad) (T.CaseA T.Owned x [] (Just (d,done))) `shouldSatisfy` isLeft
  it "preserves gapped default tags through nested matching and duplication" $ do
    let arg = n "arg"
        x = n "sum"
        y = n "selected"
        d = n "default"
        z = n "copy"
        a = n "first"
        b = n "last"
        box = T.ABox (T.VPtr T.AUnit)
        done = T.Ret T.UnitV
        body = T.Deref T.Owned (T.Var arg) x
          (T.CaseA T.Owned x [(2,y,T.Drop y done)]
            (Just (d,T.Dup d z (T.Drop d
              (T.CaseA T.Owned z [(0,a,T.Drop a done),(5,b,T.Drop b done)] Nothing)))))
        prog = program [(arg,T.Owned,T.VPtr (T.ASum [(0,box),(2,box),(5,box)]))] T.VUnit body
        cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
        (_,source,errors) = CG.cgenModule cenv prog
    TC.checkProgram prog `shouldBe` []
    TL.checkLinear prog `shouldBe` []
    errors `shouldBe` []
    source `shouldSatisfy` isInfixOf "== 3"
    [ws | line <- lines source, let ws = words line, take 1 ws == ["case"]]
      `shouldBe` [["case","1:"],["case","6:"]]
  it "splits sparse heap matches while keeping immediate defaults and ownership modes" $ do
    let arg = n "arg"
        x = n "sum"
        y = n "alternative"
        d = n "default"
        box = T.ABox (T.VPtr T.AUnit)
        done = T.Ret T.UnitV
        make mode ts i = program [(arg,if mode == T.Unique then T.Unique else T.Owned,T.VPtr (T.ASum ts))] T.VUnit
          (T.Deref (if mode == T.Unique then T.Unique else T.Owned) (T.Var arg) x
            (T.CaseA mode x [(i,y,if mode == T.Borrowed then T.Drop x done else T.Drop y done)]
              (Just (d,if mode == T.Borrowed then T.Drop x done else T.Drop d done))))
    forM_ [T.Owned,T.Borrowed,T.Unique] $ \mode ->
      forM_ [[(0,box),(1,T.AUnit)],[(0,T.AUnit),(1,box)],[(2,box),(7,T.AUnit)]] $ \ts -> do
        let i = head [j | (j,t) <- ts, t == box]
            (prog,errs) = TM.matchProgram (make mode ts i)
            cenv = CG.CEnv (T.progName prog) [] [] M.empty newtypesEmpty []
            (_,source,errors) = CG.cgenModule cenv prog
        errs `shouldBe` []
        TC.checkProgram prog `shouldBe` []
        TL.checkLinear prog `shouldBe` []
        errors `shouldBe` []
        case map T.defBody (T.progDefs prog) of
          [T.Deref _ _ _ T.SplitA{}] -> return ()
          es -> expectationFailure (show es)
        source `shouldSatisfy` isInfixOf "kk_datatype_is_ptr("
    let original = make T.Owned [(0,T.AUnit),(1,box)] 0
        (unchanged,errs) = TM.matchProgram original
    errs `shouldBe` []
    map (show . T.defBody) (T.progDefs unchanged) `shouldBe` map (show . T.defBody) (T.progDefs original)
    let sharedDefault = make T.Owned [(0,T.AUnit),(1,box),(2,box)] 1
        (stillSparse,sparseErrs) = TM.matchProgram sharedDefault
    sparseErrs `shouldBe` []
    map (show . T.defBody) (T.progDefs stillSparse) `shouldBe` map (show . T.defBody) (T.progDefs sharedDefault)
  it "checks sum partition boundaries and transfers ownership to each side" $ do
    let arg = n "arg"
        x = n "sum"
        l = n "left"
        r = n "right"
        sumType = sumA (replicate 5 (T.ABox (T.VPtr T.AUnit)))
        done = T.Ret T.UnitV
        split k mode = T.SplitA mode x k (l,T.Drop l done) (r,T.Drop r done)
        ctx = M.singleton x (T.A sumType)
        make mode = program [(arg,mode,T.VPtr sumType)] T.VUnit
                      (T.Deref mode (T.Var arg) x (split 2 mode))
    TQ.altTypes env (T.A sumType) (split 2 T.Owned) `shouldBe`
      Right [[T.A (T.ASum (take 2 (TT.sumAlts (replicate 5 (T.ABox (T.VPtr T.AUnit))))))],
             [T.A (T.ASum (drop 2 (TT.sumAlts (replicate 5 (T.ABox (T.VPtr T.AUnit))))))]]
    forM_ [-1,0,5,6] $ \k ->
      TQ.inferE env ctx M.empty (split k T.Owned) `shouldSatisfy` isLeft
    forM_ [T.Owned,T.Unique] $ \mode -> do
      TC.checkProgram (make mode) `shouldBe` []
      TL.checkLinear (make mode) `shouldBe` []
    let borrowed = program [(arg,T.Owned,T.VPtr sumType)] T.VUnit
          (T.Deref T.Owned (T.Var arg) x
            (T.SplitA T.Borrowed x 2 (l,T.Drop x done) (r,T.Drop x done)))
    TC.checkProgram borrowed `shouldBe` []
    TL.checkLinear borrowed `shouldBe` []
  it "partitions exhaustive matches and preserves sparse defaults" $ do
    let arg = n "arg"
        x = n "sum"
        d = n "default"
        box = T.ABox (T.VPtr T.AUnit)
        done = T.Ret T.UnitV
        make ts alts def = program [(arg,T.Owned,T.VPtr (sumA ts))] T.VUnit
          (T.Deref T.Owned (T.Var arg) x (T.CaseA T.Owned x alts def))
        alts = [(i,n ("alt" ++ show i),T.Drop (n ("alt" ++ show i)) done) | i <- [0..5]]
    forM_ [(replicate 6 box,3),(T.AUnit : replicate 5 box,1),
           ([T.AUnit,box],1),([box,T.AUnit],1)] $ \(ts,k) -> do
      let (prog,errs) = TM.matchProgram (make ts (take (length ts) alts) Nothing)
      errs `shouldBe` []
      TC.checkProgram prog `shouldBe` []
      TL.checkLinear prog `shouldBe` []
      case map T.defBody (T.progDefs prog) of
        [T.Deref _ _ _ (T.SplitA _ _ actual _ _)] -> actual `shouldBe` k
        es -> expectationFailure (show es)
      let (again,againErrs) = TM.matchProgram prog
      againErrs `shouldBe` []
      map (show . T.defBody) (T.progDefs again) `shouldBe` map (show . T.defBody) (T.progDefs prog)
    let sparse = make (replicate 6 box) [alts !! 4] (Just (d,T.Drop d done))
    let (sparse',sparseErrs) = TM.matchProgram sparse
    sparseErrs `shouldBe` []
    map (show . T.defBody) (T.progDefs sparse') `shouldBe` map (show . T.defBody) (T.progDefs sparse)
  it "rejects an owned default that loses the sum" $ do
    let arg = n "arg"
        x = n "sum"
        y = n "alternative"
        d = n "default"
        sumType = sumA [T.ABox (T.VPtr T.AUnit),T.ABox (T.VPtr T.AUnit)]
        body = T.Deref T.Owned (T.Var arg) x
          (T.CaseA T.Owned x [(0,y,T.Drop y (T.Ret T.UnitV))] (Just (d,T.Ret T.UnitV)))
    TL.checkLinear (program [(arg,T.Owned,T.VPtr sumType)] T.VUnit body) `shouldSatisfy` (not . null)
  where
    isLeft (Left _) = True
    isLeft _ = False

-- Check the passes directly so Core optimization cannot erase the examples.
typedPassTest :: Spec
typedPassTest = describe "typed IR normalization" $ do
  let n = N.newName
      f = n "f"
      x = n "x"
      y = n "y"
      z = n "z"
      g = n "g"
      ft = T.AFun [(T.Owned,T.VUnit)] T.VUnit
      lam = T.Ptr ft (T.Lam [(x,T.Owned,T.VUnit)] T.VUnit (T.Ret (T.Var y)))
      app = T.Deref T.Owned (T.Var f) g (T.App g [T.UnitV])
      program body = T.Program (n "passes") M.empty M.empty
        [T.DefFun (n "test") [] [(y,T.Owned,T.VUnit)] T.VUnit body]
      cont body = TF.contifyProgram (program (T.Let f (T.VPtr ft) (T.Ret lam) body))
  it "closes tail-called closures over their typed captures" $ do
    let (prog,errs) = cont (T.CaseLit (T.Lit (T.LitChar 'a')) [(T.LitChar 'a',app)] app)
    errs `shouldBe` []
    TC.checkProgram prog `shouldBe` []
    case map T.defBody (T.progDefs prog) of
      [T.Join j [(p,T.Owned,T.VUnit),(q,T.Owned,T.VUnit)] (T.Ret (T.Var capture))
        (T.CaseLit _ [(_,T.Jump k [T.UnitV,T.Var arg])] (T.Jump l _))] -> do
          p `shouldBe` x
          capture `shouldBe` q
          arg `shouldBe` y
          k `shouldBe` j
          l `shouldBe` j
      body -> expectationFailure (show body)
    let (linear,rcErrs) = TP.perceusProgram prog
    rcErrs `shouldBe` []
    TC.checkProgram linear `shouldBe` []
    TL.checkLinear linear `shouldBe` []
  it "contifies closures inside a scrutinee lambda" $ do
    let nested = T.Let f (T.VPtr ft) (T.Ret lam) app
        value = T.Ptr ft (T.Lam [(x,T.Owned,T.VUnit)] T.VUnit nested)
        (prog,errs) = TF.contifyProgram (program (T.Deref T.Owned value g (T.Ret T.UnitV)))
    errs `shouldBe` []
    TC.checkProgram prog `shouldBe` []
    case map T.defBody (T.progDefs prog) of
      [T.Deref _ (T.Ptr _ (T.Lam _ _ T.Join{})) _ _] -> return ()
      es -> expectationFailure (show es)
  it "keeps escaping closures and non-tail calls as closures" $ do
    let escaping = T.Let z (T.VPtr ft) (T.Ret (T.Var f)) app
        nonTail = T.Let z T.VUnit app (T.Ret T.UnitV)
    forM_ [escaping,nonTail] $ \body -> do
      let (prog,errs) = cont body
      errs `shouldBe` []
      TC.checkProgram prog `shouldBe` []
      case map T.defBody (T.progDefs prog) of
        [T.Let h _ _ _] -> h `shouldBe` f
        e -> expectationFailure (show e)
  it "does not capture a shadowed closure capture at a jump" $ do
    let (prog,errs) = cont (T.Let y T.VUnit (T.Ret T.UnitV) app)
    errs `shouldBe` []
    TC.checkProgram prog `shouldBe` []
    case map T.defBody (T.progDefs prog) of
      [T.Let h _ _ _] -> h `shouldBe` f
      e -> expectationFailure (show e)
  it "freshens let binders when flattening nested computations" $ do
    let nested = T.Let x T.VUnit
          (T.Let y T.VUnit (T.Ret T.UnitV) (T.Ret (T.Var y))) (T.Ret (T.Var y))
        prog = TA.anfProgram (program nested)
    TC.checkProgram prog `shouldBe` []
    case map T.defBody (T.progDefs prog) of
      [T.Let q _ _ (T.Let _ _ (T.Ret (T.Var inner)) (T.Ret (T.Var outer)))] -> do
        q `shouldNotBe` y
        inner `shouldBe` q
        outer `shouldBe` y
      e -> expectationFailure (show e)

-- Exercise the module lifecycle, rather than just the output of an executable:
-- libraries need objects before any executable is built, and cached objects
-- must be reused or rebuilt together with their interfaces.
typedBuildTest :: Options -> Spec
typedBuildTest options
  = describe "build" $ it "compiles and caches both backend objects per module" $
      bracket scratch removeDirectoryRecursive $ \dir -> do
        let out = dir </> "build"
            dep = dir </> "dependency.kk"
            wrapper = dir </> "wrapper.kk"
            main = dir </> "main.kk"
            obj name = out </> name <.> if Sys.os == "mingw32" then "obj" else "o"
            exe name = out </> (name ++ if Sys.os == "mingw32" then ".exe" else "")
            baseFlags = ["-v0", "--console=raw", "--no-buildhash", "--outputdir=" ++ out, "-i" ++ dir]
            run typed args file = do
              let kflags = baseFlags ++ ["--typedc" | typed] ++ args ++ [file]
                  (cmd,argv) = if cabal options
                                 then ("cabal", ["new-run","koka","--"] ++ kflags)
                                 else ("stack", ["exec","koka"] ++
                                        [flag | sysghc options, flag <- ["--system-ghc","--skip-ghc-check"]] ++ ["--"] ++ kflags)
              (code,stdout,stderr) <- readProcessWithExitCode cmd argv ""
              unless (code == ExitSuccess) $ expectationFailure (stdout ++ stderr)
              return (trim (testSanitize "" stdout))
            dependency value = "import std/text/regex\npub fun matched() : bool\n  \"hello\".find(regex(\"ell\")).default(\"\") == \"" ++ value ++ "\"\n"
        writeFile dep (dependency "ell")
        writeFile wrapper "import dependency\npub fun result() : bool\n  dependency/matched()\n"
        writeFile main "import wrapper\nfun main()\n  println(wrapper/result())\n"
        -- Start with a C-only cache, then enable typed compilation in that same directory.
        void $ run False ["-l"] dep
        doesFileExist (obj "dependency") `shouldReturn` True
        doesFileExist (obj "kt_dependency") `shouldReturn` False
        removeFile (obj "dependency")
        void $ run False ["-l"] wrapper
        doesFileExist (obj "dependency") `shouldReturn` True
        void $ run True ["-l"] wrapper
        doesFileExist (obj "kt_dependency") `shouldReturn` True
        before <- mapM getModificationTime [obj "dependency", obj "kt_dependency"]
        void $ run True ["-l"] wrapper
        mapM getModificationTime [obj "dependency", obj "kt_dependency"] `shouldReturn` before
        -- A lost object must invalidate the interface and rebuild the module.
        removeFile (obj "kt_dependency")
        void $ run True ["-l"] wrapper
        doesFileExist (obj "kt_dependency") `shouldReturn` True
        -- The regex dependency is transitive from main, so its include paths
        -- must be handled by its own module build rather than the final link.
        run True ["-e", "--buildname=program"] main `shouldReturn` "True"
        readProcessWithExitCode (exe "program") [] "" `shouldReturn` (ExitSuccess, "True\n", "")
        readProcessWithExitCode (exe "program_typed") [] "" `shouldReturn` (ExitSuccess, "True\n", "")
        -- Give the changed source a strictly newer timestamp without sleeping.
        ifaceTime <- getModificationTime (out </> "dependency.kki")
        writeFile dep (dependency "other")
        setModificationTime dep (addUTCTime 1 ifaceTime)
        run True ["-e", "--buildname=program"] main `shouldReturn` "False"
        readProcessWithExitCode (exe "program") [] "" `shouldReturn` (ExitSuccess, "False\n", "")
        readProcessWithExitCode (exe "program_typed") [] "" `shouldReturn` (ExitSuccess, "False\n", "")
        -- A C-only rebuild leaves typed artifacts behind. Enabling typed C
        -- again must rebuild them even though their own sources are unchanged.
        typedBefore <- getModificationTime (obj "kt_dependency")
        ifaceTime <- getModificationTime (out </> "dependency.kki")
        writeFile dep (dependency "ell")
        setModificationTime dep (addUTCTime 1 ifaceTime)
        run False ["-e", "--buildname=program"] main `shouldReturn` "True"
        getModificationTime (obj "kt_dependency") `shouldReturn` typedBefore
        -- Ensure the next build tests artifact validation, not a source whose
        -- synthetic timestamp is still newer than the rebuilt interface.
        ifaceTime <- getModificationTime (out </> "dependency.kki")
        setModificationTime dep (addUTCTime (-1) ifaceTime)
        run True ["-e", "--buildname=program"] main `shouldReturn` "True"
        readProcessWithExitCode (exe "program") [] "" `shouldReturn` (ExitSuccess, "True\n", "")
        readProcessWithExitCode (exe "program_typed") [] "" `shouldReturn` (ExitSuccess, "True\n", "")
      where
        scratch = do
          root <- getTemporaryDirectory
          (path,handle) <- openTempFile root "koka-build-test"
          hClose handle
          removeFile path
          createDirectory path
          return path

-- compile all standard libraries before testing so we can run in parallel (and return the output)
precompile :: Options -> Backend -> IO String
precompile options backend
  = do let cfg = initialCfg options backend
           stdcfg = if rebuild options then cfg{ flags = flags cfg ++ ["-r", "-l"]} else cfg
       outs <- sequence
         [ runKoka stdcfg{flags = "-e" : flags stdcfg} "" "util/link-test.kk"
           -- precompile bench by compiling a dependent file (ensures correct module name resolution)
         , runKoka stdcfg "" "test/lazy/queue/bankers.kk"
           -- precompile mpat-lib so test/cgen/mpat.kk loads it from the .kki
         , runKoka stdcfg "" "test/cgen/mpat-lib.kk"
           -- precompile specbox-lib so test/cgen/specbox.kk loads it from the .kki
           -- (both carry a -O2 .flags file so they share one build directory)
         , runKoka stdcfg "" "test/cgen/specbox-lib.kk"
           -- precompile the syn-nested chain so syn-nested1 emits only its own core
         , runKoka stdcfg "" "test/parc/syn-nested1c.kk"
         ]
       when (backend == BackendC) $
         void $ runKoka stdcfg{flags = "--target=js":(flags stdcfg)} "" "util/link-test.kk" -- precompiled js libraries as well
       return (unlines outs)


specProgress = specdoc {
    exampleSucceeded = \(nesting, requirement) info -> withSuccessColor $ do
      total  <- getTotalCount
      writeLine $ showTotal total nesting requirement
      forM_ (lines info) $ \ s -> writeLine $ indentationFor ("" : nesting) ++ s

  , exampleFailed = \(nesting, requirement) info _ -> withFailColor $ do
      n <- getFailCount
      total  <- getTotalCount
      writeLine $ showTotal total nesting requirement ++ ": FAILED [" ++ show n ++ "]"
      forM_ (take 10 (lines info)) $ \ s ->
        writeLine $ indentationFor nesting ++ (take (400) s)

  , examplePending = \(nesting, requirement) info reason -> withPendingColor $ do
      total  <- getTotalCount
      writeLine $ showTotal total nesting requirement
      forM_ (lines info) $ \ s ->
        writeLine $ indentationFor nesting ++ s
      writeLine $ indentationFor nesting ++ "# PENDING: " ++ fromMaybe "No reason given" reason
} where
    showTotal total nesting req
      = let nest = (length nesting + 1) * 2
            t    = " " ++ show total
        in replicate nest ' ' ++ req ++ replicate (12 - length req) ' ' ++ t
    indentationFor nesting
      = replicate ((length nesting + 1) * 2) ' '


