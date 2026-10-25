import Goose.Lower.FinalStatements
import Goose.Lower.TypedLists
import Goose.GIR.Validate

namespace Goose.Lower.FinalStatementChecks

open Goose.Core Goose.GIR

def body (pass : Bool) : Core.Block := .mk 0
  [.assertS (.bool pass) 0, .exit (.lit .i32 7) 1] none

def implementation (pass : Bool) : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := body pass,
    summary := .unknown }

def module (profile : ArtifactProfile) (pass : Bool) : Core.Module :=
  { profile, files := #["typed-final-statements.goose"], types := #[], globals := #[],
    impls := #[implementation pass], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "assert"⟩, ⟨0, 2, "exit"⟩] }

theorem body_simulation (cfg : Cfg) (pass : Bool) :
    TypedBlockLoopSimulation 8 cfg [] none [] [] false (body pass) := by
  apply typedBlockLoopSimulation_succ
  · apply typedStatementsLoopSimulation_cons
    · exact typedStatementLoopSimulation_assert (typedExprClaim_bool _ cfg [] pass)
    · apply typedStatementsLoopSimulation_cons
      · exact typedStatementLoopSimulation_exit (typedExprClaim_lit _ cfg [] .i32 7)
      · exact typedStatementsLoopSimulation_nil _ cfg [] none
  · trivial

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [true, false].all fun pass =>
  match Core.validate (module artifact pass), GIR.validate (lower (module artifact pass)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile => [true, false].all fun pass =>
    match Core.eval 30 profile (module artifact pass), GIR.run 60 profile (lower (module artifact pass)) with
    | .done (.exited 7) "", .done (.exited 7) "" => pass
    | .done (.aborted .assert 0) "", .done (.aborted .assert 0) "" => !pass
    | _, _ => false

end Goose.Lower.FinalStatementChecks
