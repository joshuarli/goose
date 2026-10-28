import Goose.Proofs.ConstructionAcceptedStdout
import Goose.Proofs.ConstructionScalarPrintRuntime
import Goose.Proofs.ConstructionAcceptedTerminalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem evalValue_visibleLocal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (root : Goose.Core.RootInst) (value : Value) (state : ExecutionState)
    (resolved : rootOf environment id state = .ok root state) (found : state.objects.lookup root = some value) :
    evalValue (fuel + 2) config environment (.read (.var id)) state = .ok value state := by
  simp [evalValue, evalPlace, readLoc, readValuePath, EvalM.get, bind, resolved, found, pure]

theorem execStmt_print_visibleScalar_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (origin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmt fuel config frame.interpretation.environment (.print [.expr (.read (.var id))] origin) state) := by
  obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
  have typingDeclared : frame.typing.variables[id]? = some descriptor := by
    rw [← source.compatible.variables]; exact declared
  have scalarType := scalar descriptor typingDeclared
  cases fuel with
  | zero =>
    simp [execStmt, timeout, EvalM.stop, StatementWorldOutcome]
    exact ⟨ambient, types, live, regions, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [execStmt, evalPrintArg, timeout, EvalM.stop, bind, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [execStmt, evalPrintArg, evalValue, timeout, EvalM.stop, bind, StatementWorldOutcome]
        exact ⟨ambient, types, live, regions, world⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          simp [execStmt, evalPrintArg, evalValue, evalPlace, timeout, EvalM.stop, bind, StatementWorldOutcome]
          exact ⟨ambient, types, live, regions, world⟩
        | succ fuel =>
          have evaluated := evalValue_visibleLocal fuel config frame.interpretation.environment id root value state resolved found
          rcases scalarType with ⟨intTy, same⟩ | same
          · rw [same] at represented
            cases represented with
            | integer intTy number =>
              have printed := execStmt_print_integer (fuel + 1) config frame.interpretation.environment (.read (.var id)) origin state intTy number evaluated
              simp only [printed, StatementWorldOutcome]
              let bytes := (toString number).toUTF8 ++ "\n".toUTF8
              exact ⟨trivial, frame, types, live, regions, rfl, by simpa [bytes, appendStdoutState] using world.appendStdout config frame.initialized state ambient types live regions pending bytes,
                by simpa [bytes, appendStdoutState] using source.appendStdout bytes⟩
            | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
          · rw [same] at represented
            cases represented with
            | boolean value =>
              have printed := execStmt_print_boolean (fuel + 1) config frame.interpretation.environment (.read (.var id)) origin state value evaluated
              simp only [printed, StatementWorldOutcome]
              let bytes := (if value then "true".toUTF8 else "false".toUTF8) ++ "\n".toUTF8
              exact ⟨trivial, frame, types, live, regions, rfl, by simpa [bytes, appendStdoutState] using world.appendStdout config frame.initialized state ambient types live regions pending bytes,
                by simpa [bytes, appendStdoutState] using source.appendStdout bytes⟩
            | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed

#print axioms evalValue_visibleLocal
#print axioms execStmt_print_visibleScalar_world
end Goose.Proofs.ConstructionAcceptedExecution
