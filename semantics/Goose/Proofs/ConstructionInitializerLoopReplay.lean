import Goose.Proofs.ConstructionInvocationReplay

namespace Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay

def discardValues : ExecutionStep (List Unit) → ExecutionStep PUnit
  | .ok _ state => .ok PUnit.unit state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem replay_forIn {action : α → EvalM Unit} {offset : Nat} {inputs : List α}
    {before : ExecutionState} {outcome : ExecutionStep (List Unit)} {visits : List (Invocation α Unit)}
    (replay : OperandReplay action offset inputs [] before outcome visits) :
    (forIn inputs PUnit.unit fun item _ => do
      action item
      pure (.yield PUnit.unit)) before = discardValues outcome := by
  have general : ∀ {offset : Nat} {inputs : List α} {acc : List Unit} {before : ExecutionState}
      {outcome : ExecutionStep (List Unit)} {visits : List (Invocation α Unit)},
      OperandReplay action offset inputs acc before outcome visits →
      (forIn inputs PUnit.unit fun item _ => do
        action item
        pure (.yield PUnit.unit)) before = discardValues outcome := by
    intro offset inputs acc before outcome visits replay
    induction replay with
    | done => rfl
    | next head tail ih =>
      simp only [List.forIn_cons, bind, head, pure]
      exact ih
    | stopped head | escaped head | jumped head =>
      simp only [List.forIn_cons, bind, head, discardValues]
  exact general replay

theorem initializerLoop_replay (action : α → EvalM Unit) (inputs : List α)
    (before : ExecutionState) :
    ∃ outcome visits, OperandReplay action 0 inputs [] before outcome visits ∧
      (forIn inputs PUnit.unit fun item _ => do
        action item
        pure (.yield PUnit.unit)) before = discardValues outcome ∧
      visits.map Invocation.operand = inputs.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup := by
  obtain ⟨visits, replay⟩ := mapM_replay action inputs before
  exact ⟨_, visits, replay, replay_forIn replay, replay.sourceOrder, replay.once⟩

theorem arrayLiteral_execution_replay (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementTypeFound : elementType pending.capability.logicalType = some element) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement fuel config environment current element operand)
        0 operands [] ready outcome visits ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      buildExpr (fuel + 1) config environment incoming (.arrLit ty operands origin) initial =
        protectDestination origin current (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction origin current finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) prepared := by
  obtain ⟨outcome, visits, replay, loop, ordered, once⟩ := initializerLoop_replay
    (fun operand => buildElement fuel config environment current element operand) operands ready
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  simp only [buildExpr, expressionOrigin, bind, renewed, protectDestination, found, elementTypeFound]
  simp only [bind] at loop
  rw [loop]
  cases outcome <;> rfl

theorem fixedElementFill_execution (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming current : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
    (initial ready : ExecutionState) (fixed : element.nonfixed = false)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current ready) :
    buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) initial =
      protectDestination origin current (do
        let value ← evalValue fuel config environment operand
        let bytes ← liftExcept (fixedBytes fuel config.layout element value)
        for _ in [0:count] do
          receivingAction origin current (fun destination => writeElement destination bytes)
        receivingAction origin current finishDestination) ready := by
  simp only [buildExpr, expressionOrigin, bind, renewed, fixed, Bool.false_eq_true, ↓reduceIte]

theorem nonfixedElementFill_execution (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming current : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
    (initial ready : ExecutionState) (nonfixed : element.nonfixed = true)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current ready) :
    buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) initial =
      protectDestination origin current (do
        let source ← newDestination config.layout environment.act element .value origin
        buildExpr fuel config environment source operand
        let source ← completedReceivingDestination source
        for _ in [0:count] do
          repeatElement fuel config.layout current element source origin
        receivingAction origin current (fun destination => retireRepeatedSource destination source)
        receivingAction origin current finishDestination) ready := by
  simp only [buildExpr, expressionOrigin, bind, renewed, nonfixed, ↓reduceIte]

#print axioms nonfixedElementFill_execution
#print axioms fixedElementFill_execution
private def outputThenStop (byte : UInt8) : EvalM Unit :=
  if byte = 0 then EvalM.stop .timeout else emitStdout ⟨#[byte]⟩

theorem initializerLoop_sideEffectWitness :
    ∃ state, (forIn [65, 0, 66] PUnit.unit fun byte _ => do
      outputThenStop byte
      pure (.yield PUnit.unit)) .initial = .stop .timeout state ∧
      state.construction.stdout.data.toList = [65] := by
  refine ⟨(match (forIn [65, 0, 66] PUnit.unit fun byte _ => do
    outputThenStop byte
    pure (.yield PUnit.unit)) .initial with
    | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state), ?_, ?_⟩ <;>
    unfold outputThenStop <;> cbv

#print axioms initializerLoop_sideEffectWitness
#print axioms arrayLiteral_execution_replay
#print axioms initializerLoop_replay
end Goose.Proofs.ConstructionInitializerLoopReplay
