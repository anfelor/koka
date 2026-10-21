-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Typed( typedFromCore ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Common.Unique
import Common.Name
import Common.Syntax( Platform, Fip )
import qualified Common.Syntax as Syntax
import Kind.Newtypes
import qualified Core.Core as C
import Backend.Typed.Syntax
import Backend.Typed.Passes.Contify( contifyProgram )
import Backend.Typed.Elab.Match( matchCore )
import Backend.Typed.Passes.Anf( anfProgram )
import Backend.Typed.Elab.FromCore( elabProgram )
import Backend.Typed.Check( checkProgram )
import Backend.Typed.Passes.Simplify( simplifyProgram )
import Backend.Typed.Passes.Yields( yieldsProgram )
import Backend.Typed.Passes.Perceus( perceusProgram )
import Backend.Typed.Passes.Lazy( lazyProgram )
import Backend.Typed.Passes.Reuse( reuseProgram )
import Backend.Typed.Passes.ExpandReuse( expandReuseProgram )
import Backend.Typed.Passes.CopyReset( copyResetProgram )
import Backend.Typed.Passes.DropSpec( dropSpecProgram )
import Backend.Typed.Passes.Match( matchProgram )
import Backend.Typed.Passes.SinkJoins( sinkJoinsProgram )
import Backend.Typed.Passes.JoinArgs( joinArgsProgram )
import Backend.Typed.Passes.Inline( inlineProgram )
import Backend.Typed.Passes.Paths( pathsProgram )
import Backend.Typed.Passes.Hoist( hoistProgram )
import Backend.Typed.Passes.OrderFields( orderFieldsProgram )
import Backend.Typed.Linear( checkLinear )
import Backend.Typed.Fip( checkFip )

-- returns the program after Perceus (and reuse) and messages labeled by the phase that produced them
typedFromCore :: Platform -> Bool -> Newtypes -> [C.Core] -> Int -> C.Core -> (Program,[(String,String)])
typedFromCore platform enableReuse nt imports uniq core
  = let (acore,_)              = runUnique uniq (matchCore nt core)
        (eprog,elabErrs,notes) = elabProgram platform nt imports acore
        prog                   = pathsProgram eprog
        passes                 = [("anf",False,pure' anfProgram), ("contify",False,contifyProgram), ("simplify",False,pure' simplifyProgram), ("yields",False,pure' yieldsProgram), ("perceus",True,perceusProgram), ("lazy",True,lazyProgram)
                                   ,("dropspec",True,dropSpecProgram)] ++ [("reuse",True,reuseProgram) | enableReuse]
                                   ++ [("match",True,matchProgram), ("sinkjoins",True,pure' sinkJoinsProgram), ("joinargs",True,pure' joinArgsProgram)]
                                   ++ concat [[("copyreset",True,pure' copyResetProgram),("expandreuse",True,pure' expandReuseProgram)] | enableReuse] ++ [("inline",True,inlineProgram)]
        (dsprog,msgs)          = runPasses prog (label "check" (checkProgram prog)) passes
        -- without reuse every constructor allocates
        fipMsgs                = if enableReuse && null msgs then label "fip" (checkFip (fipsOf (core:imports)) (groupsOf core) dsprog) else []
        (ordered,orderMsgs)    = if null elabErrs && null msgs then runPasses dsprog [] [("orderfields",True,orderFieldsProgram),("hoist",True,hoistProgram)] else (dsprog,[])
    in (ordered, label "elab" elabErrs ++ msgs ++ fipMsgs ++ orderMsgs ++ label "note" notes)
  where
    pure' f prog = (f prog,[])

-- the FIP annotations of the functions
fipsOf :: [C.Core] -> M.Map Name Fip
fipsOf cores
  = M.fromList ([(C.defName d, fip) | c <- cores, d <- C.flattenDefGroups (C.coreProgDefs c), Syntax.DefFun _ fip <- [C.defSort d]]
                ++ [(C.externalName x, C.externalFip x) | c <- cores, x@(C.External{}) <- C.coreProgExternals c])

-- the recursive group of each recursive definition
groupsOf :: C.Core -> M.Map Name (S.Set Name)
groupsOf core
  = M.fromList [(C.defName d, names) | C.DefRec ds <- C.coreProgDefs core, let names = S.fromList (map C.defName ds), d <- ds]

-- a pass on the typed IR: its name, whether its result must be linear, and the pass
type Pass = (String, Bool, Program -> (Program,[String]))

-- Each pass preserves path naming; validate its result directly, and check linearity
-- if the pass produces linear code. Stop at the first error so that later passes
-- never run on invalid input and the message identifies the pass responsible.
runPasses :: Program -> [(String,String)] -> [Pass] -> (Program,[(String,String)])
runPasses prog msgs _ | not (null msgs) = (prog,msgs)
runPasses prog msgs [] = (prog,msgs)
runPasses prog msgs ((name,linear,pass):passes)
  = let (prog',errs) = pass prog
        checkErrs    = label ("check after " ++ name) (checkProgram prog')
        linErrs      = if linear && null checkErrs then label ("linear after " ++ name) (checkLinear prog') else []
        msgs'        = msgs ++ label name errs
    in runPasses prog' (msgs' ++ (if null msgs' then checkErrs ++ linErrs else [])) passes

label :: String -> [String] -> [(String,String)]
label l msgs = [(l,msg) | msg <- msgs]
