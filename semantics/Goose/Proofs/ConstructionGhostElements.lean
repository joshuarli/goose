import Goose.Proofs.ConstructionGhostElementCore
import Goose.Proofs.ConstructionGhostInvocation
import Goose.Proofs.ConstructionInitializerLoopReplay

namespace Goose.Proofs.ConstructionGhostElements
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay

inductive FixedElementTree (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) :
    Nat → List Nat → Expr → ExecutionState → ExecutionStep Unit → Prop
  | source (fuel : Nat) (path : List Nat) (operand : Expr) (before : ExecutionState)
      (fixed : element.nonfixed = false)
      (tree : EvaluationTree config environment fuel (path ++ [0]) operand before
        (evalValue fuel config environment operand before)) :
      FixedElementTree config environment parent element (fuel + 1) path operand before
        (fixedElementContinuation fuel config parent element operand
          (evalValue fuel config environment operand before))

theorem fixedElementTree_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (path : List Nat) (operand : Expr)
    (before : ExecutionState) (fixed : element.nonfixed = false) :
    FixedElementTree config environment parent element (fuel + 1) path operand before
      (buildElement (fuel + 1) config environment parent element operand before) := by
  rw [fixedElement_execution fuel config environment parent element operand before fixed]
  exact .source fuel path operand before fixed (evaluationTree_exists fuel config environment _ _ _)

theorem fixedElementTree_sound {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {parent : Goose.Core.DestinationId} {element : Ty} {path : List Nat} {operand : Expr}
    {before : ExecutionState} {outcome : ExecutionStep Unit}
    (tree : FixedElementTree config environment parent element fuel path operand before outcome) :
    buildElement fuel config environment parent element operand before = outcome := by
  cases tree with
  | source fuel path operand before fixed tree =>
    exact fixedElement_execution fuel config environment parent element operand before fixed

theorem arrayLiteral_fixedElements_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) (path : List Nat)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (fixed : element.nonfixed = false)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementTypeFound : elementType pending.capability.logicalType = some element) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand)
        0 operands [] ready outcome visits ∧
      (∀ visit ∈ visits, FixedElementTree config environment current element (fuel + 1)
        (visit.path path) visit.operand visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      buildExpr (fuel + 2) config environment incoming (.arrLit ty operands origin) initial =
        protectDestination origin current (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction origin current finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) prepared := by
  obtain ⟨outcome, visits, replay, order, once, execution⟩ :=
    arrayLiteral_execution_replay (fuel + 1) config environment incoming current ty operands origin
      initial prepared ready pending element renewed found elementTypeFound
  refine ⟨outcome, visits, replay, ?_, order, once, execution⟩
  intro visit member
  rw [← visit_executes replay visit member]
  exact fixedElementTree_exists fuel config environment current element (visit.path path)
    visit.operand visit.before fixed

private def arrayWitness : EvalM Unit := do
  let config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
  let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
  let ty := Ty.varr (.int .i64)
  let destination ← newDestination config.layout environment.act ty .value 0
  buildExpr 40 config environment destination (.arrLit ty
    [.blockE (.mk 0 [.print [.text "once"] 0] (some (.lit .i64 7))) 0, .lit .i64 8] 0)

private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem arrayWitness_sideEffect :
    ∃ state, arrayWitness .initial = .ok () state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (arrayWitness .initial), ?_, ?_⟩ <;> unfold arrayWitness stepState <;> cbv

#print axioms arrayWitness_sideEffect
#print axioms arrayLiteral_fixedElements_ghost
#print axioms fixedElementTree_exists
#print axioms fixedElementTree_sound
end Goose.Proofs.ConstructionGhostElements
