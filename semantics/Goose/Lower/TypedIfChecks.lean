import Goose.Lower.TypedIf
import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers
import Goose.GIR.Validate

namespace Goose.Lower.TypedIfChecks

open Goose.Core Goose.GIR

def returning : Core.Block := .mk 1 [.ret none 1] none

def body (branch : Bool) (both : Bool) : Core.Block := .mk 0
  [.ifS (.bool branch) returning (if both then some (.mk 2 [] none) else none) 0,
    .abort "fallthrough" 2] none

def implementation (branch both : Bool) : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := body branch both, summary := .unknown }

def module (profile : ArtifactProfile) (branch both : Bool) : Core.Module :=
  { profile, files := #["typed-if.goose"], types := #[], globals := #[],
    impls := #[implementation branch both],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "if"⟩, ⟨0, 2, "return"⟩, ⟨0, 3, "expr"⟩] }

theorem returning_simulation (fuel : Nat) (cfg : Cfg) (loop : Option LoopCtx) :
    TypedBlockLoopSimulation fuel cfg [] loop [] [] false returning := by
  cases fuel with
  | zero => exact typedBlockLoopSimulation_zero _ _ _ _ _ _ _
  | succ fuel =>
    apply typedBlockLoopSimulation_succ
    · cases fuel with
      | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
      | succ fuel =>
        apply typedStatementsLoopSimulation_cons
        · exact typedStatementLoopSimulation_return_none fuel cfg [] loop 1
        · exact typedStatementsLoopSimulation_nil fuel cfg [] loop
    · trivial

theorem body_simulation (cfg : Cfg) (branch both : Bool) :
    TypedBlockLoopSimulation 8 cfg [] none [] [] false (body branch both) := by
  apply typedBlockLoopSimulation_succ
  · apply typedStatementsLoopSimulation_cons
    · cases both with
      | false =>
        exact typedStatementLoopSimulation_if_none (typedExprClaim_bool _ cfg [] branch)
          (returning_simulation _ cfg none)
      | true =>
        exact typedStatementLoopSimulation_if_some (typedExprClaim_bool _ cfg [] branch)
          (returning_simulation _ cfg none)
          (typedBlockLoopSimulation_nil _ cfg [] none [] [] false 2)
    · apply typedStatementsLoopSimulation_cons
      · exact typedStatementLoopSimulation_abort "fallthrough" 2
      · exact typedStatementsLoopSimulation_nil _ cfg [] none
  · trivial

#guard [ArtifactProfile.pilot, .shrink].all fun profile =>
  [true, false].all fun branch => [true, false].all fun both =>
    match Core.validate (module profile branch both), GIR.validate (lower (module profile branch both)) with
    | .ok _, .ok _ => true
    | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    [true, false].all fun branch => [true, false].all fun both =>
      match Core.eval 30 profile (module artifact branch both),
          GIR.run 60 profile (lower (module artifact branch both)) with
      | .done .returned "", .done .returned "" => branch
      | .done (.aborted .userAbort 2) "", .done (.aborted .userAbort 2) "" => !branch
      | _, _ => false

end Goose.Lower.TypedIfChecks
