import Goose.Proofs.ConstructionAcceptedIntegerAssignment
import Goose.Proofs.ConstructionAcceptedScalarPrint

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def localIntegerAssignments (id : Nat) (intTy : Goose.Core.IntTy) (assignments : List (Int × Goose.Core.OriginId)) : List Stmt :=
  assignments.map (fun assignment => .assign (.var id) (.lit intTy assignment.1) assignment.2)

theorem execStmts_integerAssignments_print_world (assignments : List (Int × Goose.Core.OriginId)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id : Nat) (intTy : Goose.Core.IntTy)
    (printOrigin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (localType : ∀ descriptor, frame.typing.variables[id]? = some descriptor → descriptor.ty = .int intTy) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmts fuel config frame.interpretation.environment
        (localIntegerAssignments id intTy assignments ++ [.print [.expr (.read (.var id))] printOrigin]) state) := by
  induction assignments generalizing fuel state live with
  | nil =>
    cases fuel with
    | zero =>
      simp [localIntegerAssignments, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have printed := execStmt_print_visibleScalar_world fuel config accepted frame state ambient types live regions pending
        id printOrigin world source visible (by intro descriptor declared; exact Or.inl ⟨intTy, localType descriptor declared⟩)
      simpa [localIntegerAssignments] using execStmts_terminal_world fuel config accepted frame frame.interpretation.environment
        (.print [.expr (.read (.var id))] printOrigin) state ambient pending printed
  | cons assignment rest ih =>
    obtain ⟨number, origin⟩ := assignment
    cases fuel with
    | zero =>
      simp [localIntegerAssignments, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have head := execStmt_assignVisibleInteger_complete fuel config accepted frame state ambient types live regions pending
        id intTy number origin world source visible initialized bounded localType
      cases executed : execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state with
      | escape target carriers after | jump target kind after =>
        simp only [executed] at head
        obtain ⟨_, _, _, impossible⟩ := head
        exact impossible.elim
      | stop reason after =>
        simp only [executed, Goose.Proofs.Exit.stepState] at head
        obtain ⟨nextLive, nextWorld, nextSource, flow⟩ := head
        simp only [localIntegerAssignments, List.map_cons, List.cons_append, execStmts, bind, executed, StatementWorldOutcome]
        exact ⟨ambient, types, nextLive, regions, nextWorld⟩
      | ok flow after =>
        simp only [executed, Goose.Proofs.Exit.stepState] at head
        obtain ⟨nextLive, nextWorld, nextSource, normal⟩ := head
        subst flow
        have result := ih fuel after nextLive nextWorld nextSource
        simpa only [localIntegerAssignments, List.map_cons, List.cons_append, execStmts, bind, executed] using result

#print axioms execStmts_integerAssignments_print_world
end Goose.Proofs.ConstructionAcceptedExecution
