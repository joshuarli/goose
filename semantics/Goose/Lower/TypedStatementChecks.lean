import Goose.Lower.TypedStatements
import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers
import Goose.GIR.Validate

namespace Goose.Lower.TypedStatementChecks

open Goose.Core Goose.GIR

def borrowed : Expr := .ref .mutable (.global 0)

def body : Core.Block := .mk 0
  [.letS 0 borrowed 0, .rebind 0 borrowed 0, .expr borrowed 0, .ret none 0] none

def implementation : Impl :=
  { name := "main", params := #[], results := #[],
    vars := #[⟨"r", .ref .readOnly (.int .i64), .mutable, 0, 0⟩],
    body, summary := .unknown }

def module (profile : ArtifactProfile) : Core.Module :=
  { profile, files := #["typed-statements.goose"], types := #[],
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩],
    impls := #[implementation], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem borrowed_simulation (fuel : Nat) (cfg : Cfg) (results : List Ty) :
    TypedExprClaim fuel cfg results borrowed := by
  cases fuel with
  | zero => exact typedExprClaim_zero _ _ _
  | succ fuel => exact typedExprClaim_ref (typedPlaceClaim_global fuel cfg results 0) .mutable

theorem body_simulation (cfg : Cfg) :
    TypedBlockLoopSimulation 8 cfg [] none [] [] false body := by
  apply typedBlockLoopSimulation_succ
  · apply typedStatementsLoopSimulation_cons
    · exact typedStatementLoopSimulation_let (borrowed_simulation _ cfg [])
    · apply typedStatementsLoopSimulation_cons
      · exact typedStatementLoopSimulation_rebind (borrowed_simulation _ cfg [])
      · apply typedStatementsLoopSimulation_cons
        · exact typedStatementLoopSimulation_expr (borrowed_simulation _ cfg [])
        · apply typedStatementsLoopSimulation_cons
          · exact typedStatementLoopSimulation_return_none _ cfg [] none 0
          · exact typedStatementsLoopSimulation_nil _ cfg [] none
  · trivial

#guard [ArtifactProfile.pilot, .shrink].all fun profile =>
  match Core.validate (module profile), GIR.validate (lower (module profile)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 30 profile (module artifact), GIR.run 60 profile (lower (module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

end Goose.Lower.TypedStatementChecks
