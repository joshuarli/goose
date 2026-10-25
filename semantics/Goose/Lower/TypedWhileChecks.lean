import Goose.Lower.TypedWhile
import Goose.Lower.TypedStatements
import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers
import Goose.GIR.Validate

namespace Goose.Lower.TypedWhileChecks

open Goose.Core Goose.GIR

def borrowed (globalId : GlobalId) : Expr := .ref .readOnly (.global globalId)

def condition : Expr := .read (.deref (.read (.var 0)))

def iteration : Core.Block := .mk 1 [.rebind 0 (borrowed 1) 1, .cont 2] none

def body : Core.Block := .mk 0 [.letS 0 (borrowed 0) 0, .while condition iteration 3] none

def implementation : Impl :=
  { name := "main", params := #[], results := #[],
    vars := #[⟨"again", .ref .readOnly .bool, .mutable, 0, 0⟩], body, summary := .unknown }

def module (profile : ArtifactProfile) : Core.Module :=
  { profile, files := #["typed-while.goose"], types := #[],
    globals := #[⟨"yes", .bool, .immutable, .bool true, 0⟩,
      ⟨"no", .bool, .immutable, .bool false, 0⟩],
    impls := #[implementation], contexts := #[⟨0, "main", [(0, [.global 0, .global 1])], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "let"⟩, ⟨0, 2, "rebind"⟩, ⟨0, 3, "continue"⟩, ⟨0, 4, "while"⟩] }

theorem borrowed_simulation (fuel : Nat) (cfg : Cfg) (globalId : GlobalId) :
    TypedExprClaim fuel cfg [] (borrowed globalId) := by
  cases fuel with
  | zero => exact typedExprClaim_zero _ _ _
  | succ fuel => exact typedExprClaim_ref (typedPlaceClaim_global fuel cfg [] globalId) .readOnly

theorem reference_simulation (fuel : Nat) (cfg : Cfg) :
    TypedExprClaim fuel cfg [] (.read (.var 0)) := by
  cases fuel with
  | zero => exact typedExprClaim_zero _ _ _
  | succ fuel => exact typedExprClaim_read (typedPlaceClaim_var fuel cfg [] 0)

theorem dereference_simulation (fuel : Nat) (cfg : Cfg) :
    TypedPlaceClaim fuel cfg [] (.deref (.read (.var 0))) := by
  cases fuel with
  | zero => exact typedPlaceClaim_zero _ _ _
  | succ fuel => exact typedPlaceClaim_deref (reference_simulation fuel cfg)

theorem condition_simulation (fuel : Nat) (cfg : Cfg) : TypedExprClaim fuel cfg [] condition := by
  cases fuel with
  | zero => exact typedExprClaim_zero _ _ _
  | succ fuel => exact typedExprClaim_read (dereference_simulation fuel cfg)

theorem iteration_simulation (fuel : Nat) (cfg : Cfg) (context : LoopCtx) :
    TypedBlockLoopSimulation fuel cfg [] (some context) [] [] false iteration := by
  cases fuel with
  | zero => exact typedBlockLoopSimulation_zero _ _ _ _ _ _ _
  | succ fuel =>
    apply typedBlockLoopSimulation_succ
    · cases fuel with
      | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
      | succ fuel =>
        apply typedStatementsLoopSimulation_cons
        · cases fuel with
          | zero => exact typedStatementLoopSimulation_zero _ _ _ _
          | succ fuel =>
            exact typedStatementLoopSimulation_rebind (borrowed_simulation fuel cfg 1)
        · cases fuel with
          | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
          | succ fuel =>
            apply typedStatementsLoopSimulation_cons
            · exact typedStatementLoopSimulation_continue fuel cfg [] (some context) 2
            · exact typedStatementsLoopSimulation_nil fuel cfg [] (some context)
    · trivial

theorem header_simulation (fuel : Nat) (cfg : Cfg) :
    TypedWhileSimulation fuel cfg [] condition iteration 3 := by
  induction fuel with
  | zero => exact typedWhileSimulation_zero _ _ _ _ _
  | succ fuel previous =>
    exact typedWhileSimulation_succ (condition_simulation fuel cfg)
      (iteration_simulation fuel cfg) previous

theorem body_simulation (cfg : Cfg) :
    TypedBlockLoopSimulation 10 cfg [] none [] [] false body := by
  apply typedBlockLoopSimulation_succ
  · apply typedStatementsLoopSimulation_cons
    · exact typedStatementLoopSimulation_let (borrowed_simulation _ cfg 0)
    · apply typedStatementsLoopSimulation_cons
      · exact typedStatementLoopSimulation_while (header_simulation _ cfg)
      · exact typedStatementsLoopSimulation_nil _ cfg [] none
  · trivial

#guard [ArtifactProfile.pilot, .shrink].all fun profile =>
  match Core.validate (module profile), GIR.validate (lower (module profile)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 40 profile (module artifact), GIR.run 80 profile (lower (module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

end Goose.Lower.TypedWhileChecks
