-----------------------------------------------------------------------------
-- Copyright 2026, Microsoft Research, Daan Leijen, Anton Lorenzen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

module Backend.Typed.Typed( typedFromCore ) where

import Common.Unique
import Common.Syntax( Platform )
import Kind.Newtypes
import qualified Core.Core as C
import Backend.Typed.Syntax
import Backend.Typed.Passes.Contify( contifyProgram )
import Backend.Typed.Elab.Match( matchCore )
import Backend.Typed.Passes.Anf( anfProgram )
import Backend.Typed.Elab.FromCore( elabProgram )
import Backend.Typed.Check( checkProgram )
import Backend.Typed.Passes.Simplify( simplifyProgram )
import Backend.Typed.Passes.Perceus( perceusProgram )
import Backend.Typed.Passes.Lazy( lazyProgram )
import Backend.Typed.Passes.Reuse( reuseProgram )
import Backend.Typed.Passes.DropSpec( dropSpecProgram )
import Backend.Typed.Passes.Match( matchProgram )
import Backend.Typed.Passes.SinkJoins( sinkJoinsProgram )
import Backend.Typed.Passes.JoinArgs( joinArgsProgram )
import Backend.Typed.Linear( checkLinear )

-- returns the program after Perceus (and reuse) and messages labeled by the phase that produced them
typedFromCore :: Platform -> Bool -> Newtypes -> [C.Core] -> Int -> C.Core -> (Program,[(String,String)])
typedFromCore platform enableReuse nt imports uniq core
  = let (acore,_)             = runUnique uniq (matchCore nt core)
        (prog,elabErrs,notes) = elabProgram platform nt imports acore
        passes                = [("anf",False,pure' anfProgram), ("contify",False,contifyProgram), ("simplify",False,pure' simplifyProgram), ("perceus",True,perceusProgram), ("lazy",True,lazyProgram)
                                  ,("dropspec",True,dropSpecProgram)] ++ [("reuse",True,reuseProgram) | enableReuse]
                                  ++ [("match",True,matchProgram), ("sinkjoins",True,pure' sinkJoinsProgram), ("joinargs",True,pure' joinArgsProgram)]
        (dsprog,msgs)         = runPasses prog (label "check" (checkProgram prog)) passes
    in (dsprog, label "elab" elabErrs ++ msgs ++ label "note" notes)
  where
    pure' f prog = (f prog,[])

-- a pass on the typed IR: its name, whether its result must be linear, and the pass
type Pass = (String, Bool, Program -> (Program,[String]))

-- after each pass the program is type checked and, if the pass produces linear code, checked
-- for linearity; the checks stop at the first error so that it names the pass that caused it
runPasses :: Program -> [(String,String)] -> [Pass] -> (Program,[(String,String)])
runPasses prog msgs [] = (prog,msgs)
runPasses prog msgs ((name,linear,pass):passes)
  = let (prog',errs) = pass prog
        checkErrs    = label ("check after " ++ name) (checkProgram prog')
        linErrs      = if linear && null checkErrs then label ("linear after " ++ name) (checkLinear prog') else []
        msgs'        = msgs ++ label name errs
    in runPasses prog' (msgs' ++ (if null msgs' then checkErrs ++ linErrs else [])) passes

label :: String -> [String] -> [(String,String)]
label l msgs = [(l,msg) | msg <- msgs]
