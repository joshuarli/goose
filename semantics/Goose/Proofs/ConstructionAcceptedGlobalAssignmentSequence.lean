import Goose.Proofs.ConstructionAcceptedIntegerAssignment
import Goose.Proofs.ConstructionAcceptedScalarPrint

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

structure GlobalIntegerAssignment where
  id : Nat
  intTy : Goose.Core.IntTy
  number : Int
  origin : Goose.Core.OriginId

def globalIntegerAssignments (assignments : List GlobalIntegerAssignment) : List Stmt :=
  assignments.map (fun assignment => .assign (.global assignment.id) (.lit assignment.intTy assignment.number) assignment.origin)

theorem execStmts_globalAssignments_printLocal_world (assignments : List GlobalIntegerAssignment) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id : Nat) (printOrigin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (targets : ∀ assignment ∈ assignments, ∃ descriptor, config.module.globals[assignment.id]? = some descriptor ∧
      descriptor.ty = .int assignment.intTy) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmts fuel config frame.interpretation.environment
        (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var id))] printOrigin]) state) := by
  induction assignments generalizing fuel state with
  | nil =>
    cases fuel with
    | zero =>
      simp [globalIntegerAssignments, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have printed := execStmt_print_visibleScalar_world fuel config accepted frame state ambient types live regions pending
        id printOrigin world source visible localScalar
      simpa [globalIntegerAssignments] using execStmts_terminal_world fuel config accepted frame frame.interpretation.environment
        (.print [.expr (.read (.var id))] printOrigin) state ambient pending printed
  | cons assignment rest ih =>
    cases fuel with
    | zero =>
      simp [globalIntegerAssignments, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨descriptor, declared, scalar⟩ := targets assignment (by simp)
      have head := execStmt_assignGlobalInteger_complete fuel config accepted frame state ambient types live regions pending
        assignment.id assignment.intTy assignment.number assignment.origin descriptor world source initialized bounded declared scalar
      cases executed : execStmt fuel config frame.interpretation.environment
          (.assign (.global assignment.id) (.lit assignment.intTy assignment.number) assignment.origin) state with
      | escape target carriers after | jump target kind after => simp only [executed] at head; exact head.2.2.elim
      | stop reason after =>
        simp only [executed, Goose.Proofs.Exit.stepState] at head
        simp only [globalIntegerAssignments, List.map_cons, List.cons_append, execStmts, bind, executed, StatementWorldOutcome]
        exact ⟨ambient, types, live, regions, head.1⟩
      | ok flow after =>
        simp only [executed, Goose.Proofs.Exit.stepState] at head
        obtain ⟨nextWorld, nextSource, normal⟩ := head
        subst flow
        have remaining : ∀ item ∈ rest, ∃ descriptor, config.module.globals[item.id]? = some descriptor ∧
            descriptor.ty = .int item.intTy := by
          intro item member; exact targets item (List.mem_cons_of_mem assignment member)
        have result := ih fuel after nextWorld nextSource remaining
        simpa only [globalIntegerAssignments, List.map_cons, List.cons_append, execStmts, bind, executed] using result

#print axioms execStmts_globalAssignments_printLocal_world
end Goose.Proofs.ConstructionAcceptedExecution
