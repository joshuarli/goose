import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate

namespace Goose.Lower.Validation.CfgChecks

open Goose

private def stoppedDiamond : Core.Impl :=
  { name := "stop"
    params := #[]
    results := #[]
    vars := #[]
    body := .mk 0 [.expr (.ifE (.bool true) (.mk 1 [] (some (.bool true)))
      (.mk 2 [] (some (.bool false)))) 0, .abort "stop" 0] none
    summary := .unknown }

private def stoppedModule : Core.Module :=
  { files := #["test"]
    types := #[]
    globals := #[]
    impls := #[stoppedDiamond]
    contexts := #[⟨0, "stop", [], [], []⟩]
    entry := 0
    origins := #[⟨0, 1, "abort"⟩] }


private def stoppedCaller : Core.Impl :=
  { name := "main"
    params := #[]
    results := #[]
    vars := #[]
    body := .mk 0 [.expr (.call 0 [] 0) 0] none
    summary := .unknown }

private def stoppedCallerModule : Core.Module :=
  { stoppedModule with
    impls := #[stoppedDiamond, stoppedCaller]
    contexts := #[⟨0, "stop", [], [], []⟩, ⟨1, "main", [], [], []⟩]
    entry := 1 }

#guard (Core.validate stoppedCallerModule).toBool
#guard stoppedCallerModule.noReturn 0
#guard (Lower.lowerImpl stoppedCallerModule stoppedDiamond).blocks.size == 4
#guard !(GIR.funcMayReturn #[true, true] (Lower.lowerImpl stoppedCallerModule stoppedDiamond))
#guard (Lower.lower stoppedCallerModule).functionsMayReturn == #[false, false]
#guard (GIR.validate (Lower.lower stoppedCallerModule)).toBool

private def returning : GIR.Func :=
  { name := "returning"
    params := []
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[], [.term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def looping : GIR.Func :=
  { returning with
    name := "looping"
    blocks := #[⟨[], [.term (.br 1 [])]⟩, ⟨[], [.term (.br 1 [])]⟩] }

private def duplicatedTarget : GIR.Func :=
  { returning with
    name := "duplicated-target"
    blocks := #[⟨[], [.def 0 (.constBool true), .term (.condbr 0 1 [] 1 [])]⟩,
      ⟨[], [.term (.abort .userAbort none)]⟩] }

private def loopWithReturn : GIR.Func :=
  { returning with
    name := "loop-with-return"
    blocks := #[⟨[], [.def 0 (.constBool true), .term (.br 1 [])]⟩,
      ⟨[], [.term (.condbr 0 1 [] 2 [])]⟩, ⟨[], [.term (.ret [] none)]⟩] }

#guard GIR.funcMayReturn #[] returning
#guard !(GIR.funcMayReturn #[] looping)
#guard !(GIR.funcMayReturn #[] duplicatedTarget)
#guard GIR.funcMayReturn #[] loopWithReturn

private def recursiveStop : Core.Impl :=
  { stoppedCaller with body := .mk 0 [.expr (.call 0 [] 0) 0, .abort "stop" 0] none }

private def recursiveStopModule : Core.Module :=
  { stoppedModule with impls := #[recursiveStop], contexts := #[⟨0, "main", [], [], []⟩] }

private def firstMutualStop : Core.Impl :=
  { recursiveStop with name := "first", body := .mk 0 [.expr (.call 1 [] 0) 0, .abort "stop" 0] none }

private def secondMutualStop : Core.Impl :=
  { recursiveStop with name := "second" }

private def mutualStopModule : Core.Module :=
  { stoppedModule with
    impls := #[firstMutualStop, secondMutualStop]
    contexts := #[⟨0, "first", [], [], []⟩, ⟨1, "second", [], [], []⟩] }

#guard (Core.validate recursiveStopModule).toBool
#guard recursiveStopModule.noReturn 0
#guard (Lower.lower recursiveStopModule).functionsMayReturn == #[false]
#guard (GIR.validate (Lower.lower recursiveStopModule)).toBool
#guard (Core.validate mutualStopModule).toBool
#guard mutualStopModule.noReturn 0 && mutualStopModule.noReturn 1
#guard (Lower.lower mutualStopModule).functionsMayReturn == #[false, false]
#guard (GIR.validate (Lower.lower mutualStopModule)).toBool

private def recursiveBaseCase : GIR.Func :=
  { returning with
    name := "recursive-base-case"
    blocks := #[⟨[], [.def 0 (.constBool true), .term (.condbr 0 1 [] 2 [])]⟩,
      ⟨[], [.term (.ret [] none)]⟩, ⟨[], [.def 1 (.call 0 [] none), .term .unreachable]⟩] }

private def recursiveBaseCaseModule : GIR.Module :=
  { Lower.lower stoppedModule with funcs := #[recursiveBaseCase] }

private def bareUnreachable : GIR.Func :=
  { returning with name := "bare-unreachable", blocks := #[⟨[], [.term .unreachable]⟩] }

private def unknownCallee : GIR.Func :=
  { returning with name := "unknown-callee", blocks := #[⟨[], [.def 0 (.call 7 [] none), .term .unreachable]⟩] }

#guard GIR.funcMayReturn #[false] recursiveBaseCase
#guard recursiveBaseCaseModule.functionsMayReturn == #[true]
#guard !(GIR.checkUnreachableOf recursiveBaseCaseModule.functionsMayReturn "base" recursiveBaseCase).toBool
#guard !(GIR.validate recursiveBaseCaseModule).toBool
#guard GIR.funcMayReturn #[] bareUnreachable
#guard !(GIR.checkUnreachableOf #[true] "bare" bareUnreachable).toBool
#guard GIR.funcMayReturn #[] unknownCallee
#guard !(GIR.checkUnreachableOf #[] "unknown" unknownCallee).toBool

end Goose.Lower.Validation.CfgChecks
