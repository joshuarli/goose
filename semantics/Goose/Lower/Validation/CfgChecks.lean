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

end Goose.Lower.Validation.CfgChecks
