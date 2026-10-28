import Goose.Proofs.ConstructionGhostSourceTransition
import Goose.Proofs.ConstructionGhostElements

namespace Goose.Proofs.ConstructionGhostSourceElement
open Goose.Construct Goose.Proofs.ConstructionGhostSourceTransition Goose.Proofs.ConstructionGhostElements

inductive ElementHistory (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Nat → Goose.Core.DestinationId → Ty → Expr → ExecutionState → ExecutionStep Unit → Prop
  | timeout (path : List Nat) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState) :
      ElementHistory config environment 0 path parent element operand before (.stop .timeout before)
  | fixed {fuel : Nat} {path : List Nat} {parent : Goose.Core.DestinationId} {element : Ty} {operand : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value} (fixed : element.nonfixed = false)
      (child : ValueHistory config environment fuel (path ++ [0]) operand before outcome) :
      ElementHistory config environment (fuel + 1) path parent element operand before
        (fixedElementContinuation fuel config parent element operand outcome)

theorem fixedElement_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState)
    (fixed : element.nonfixed = false) :
    buildElement (fuel + 1) config environment parent element operand before =
      fixedElementContinuation fuel config parent element operand (evalValue fuel config environment operand before) :=
  fixedElement_execution fuel config environment parent element operand before fixed

theorem ElementHistory.sound
    (history : ElementHistory config environment fuel path parent element operand before outcome) :
    buildElement fuel config environment parent element operand before = outcome := by
  cases history with
  | timeout => simp [buildElement, Goose.Construct.timeout, EvalM.stop]
  | @fixed fuel path parent element operand before outcome fixed child =>
      rw [fixedElement_source fuel config environment parent element operand before fixed, child.sound]

theorem elementHistory_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState)
    (fixed : element.nonfixed = false) (supported : SupportedValue operand) :
    ElementHistory config environment fuel path parent element operand before
      (buildElement fuel config environment parent element operand before) := by
  cases fuel with
  | zero => simpa [buildElement, Goose.Construct.timeout, EvalM.stop] using
      (ElementHistory.timeout path parent element operand before :
        ElementHistory config environment 0 path parent element operand before _)
  | succ fuel =>
      rw [fixedElement_source fuel config environment parent element operand before fixed]
      exact .fixed fixed (valueHistory_exists fuel config environment (path ++ [0]) operand before supported)

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessAction : EvalM Unit := do
  let parent ← newDestination witnessConfig.layout 0 (.varr (.int .u8)) .value 0 none (some 1)
  buildElement 20 witnessConfig witnessEnvironment parent (.int .u8) (.lit .u8 7)
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem elementWitness_writes : ∃ state, witnessAction .initial = .ok () state ∧
    state.construction.events = [.begin 0, .write 0 0] := by
  refine ⟨witnessState (witnessAction .initial), ?_, ?_⟩ <;>
    unfold witnessAction witnessConfig witnessEnvironment witnessState <;> cbv

#print axioms elementWitness_writes

#print axioms fixedElement_source
#print axioms ElementHistory.sound
#print axioms elementHistory_exists
end Goose.Proofs.ConstructionGhostSourceElement
