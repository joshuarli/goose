import Goose.Proofs.ConstructionAcceptedScalarPrint

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def localReadStatements (id : Nat) (origins : List Goose.Core.OriginId) : List Stmt :=
  origins.map (fun origin => .expr (.read (.var id)) origin)

theorem execStmt_visibleLocalRead_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (origin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmt fuel config frame.interpretation.environment (.expr (.read (.var id)) origin) state) := by
  obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
  cases fuel with
  | zero =>
    simp only [execStmt, timeout, EvalM.stop, StatementWorldOutcome]
    exact ⟨ambient, types, live, regions, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [execStmt, evalValue, timeout, EvalM.stop, bind, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [execStmt, evalValue, evalPlace, timeout, EvalM.stop, bind, StatementWorldOutcome]
        exact ⟨ambient, types, live, regions, world⟩
      | succ fuel =>
        have evaluated := evalValue_visibleLocal fuel config frame.interpretation.environment id root value state resolved found
        simp [execStmt, bind, evaluated, pure, StatementWorldOutcome]
        exact ⟨frame, rfl, types, ⟨live, regions, world⟩, source⟩

theorem execStmts_localReads_print_world (origins : List Goose.Core.OriginId) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id : Nat) (printOrigin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmts fuel config frame.interpretation.environment
        (localReadStatements id origins ++ [.print [.expr (.read (.var id))] printOrigin]) state) := by
  induction origins generalizing fuel with
  | nil =>
    cases fuel with
    | zero =>
      simp [localReadStatements, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have printed := execStmt_print_visibleScalar_world fuel config accepted frame state ambient types live regions pending
        id printOrigin world source visible scalar
      simpa [localReadStatements] using execStmts_terminal_world fuel config accepted frame frame.interpretation.environment
        (.print [.expr (.read (.var id))] printOrigin) state ambient pending printed
  | cons origin rest ih =>
    cases fuel with
    | zero =>
      simp [localReadStatements, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have head := execStmt_visibleLocalRead_world fuel config accepted frame state ambient types live regions pending id origin world source visible
      cases executed : execStmt fuel config frame.interpretation.environment (.expr (.read (.var id)) origin) state with
      | escape target carriers after | jump target kind after => simp [StatementWorldOutcome, executed] at head
      | stop reason after =>
        simp only [StatementWorldOutcome, executed] at head
        simp only [localReadStatements, List.map_cons, List.cons_append, execStmts, bind, executed, StatementWorldOutcome]
        exact head
      | ok flow after =>
        simp only [StatementWorldOutcome, executed] at head
        obtain ⟨normal, next, nextTypes, nextLive, nextRegions, initialized, nextWorld, nextSource⟩ := head
        subst flow
        have actual : after = state := by
          cases fuel with
          | zero => simp [execStmt, timeout, EvalM.stop] at executed
          | succ fuel =>
            cases fuel with
            | zero => simp [execStmt, evalValue, timeout, EvalM.stop, bind] at executed
            | succ fuel =>
              cases fuel with
              | zero => simp [execStmt, evalValue, evalPlace, timeout, EvalM.stop, bind] at executed
              | succ fuel =>
                obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
                have evaluated := evalValue_visibleLocal fuel config frame.interpretation.environment id root value state resolved found
                simp [execStmt, bind, evaluated, pure] at executed
                exact executed.symm
        subst after
        simpa only [localReadStatements, List.map_cons, List.cons_append, execStmts, bind, executed] using ih fuel

#print axioms execStmt_visibleLocalRead_world
#print axioms execStmts_localReads_print_world
end Goose.Proofs.ConstructionAcceptedExecution
