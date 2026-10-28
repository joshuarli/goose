import Goose.Proofs.ConstructionGhostDeclarationSourceSegments
import Goose.Proofs.ConstructionInitializerLoopReplay

namespace Goose.Proofs.ConstructionGhostProtectedSourceEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionInitializerLoopReplay Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem protectedResult_sourcePrefix (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId)
    (action : EvalM α) (before : ExecutionState) :
    EventPrefix (Goose.Proofs.Exit.stepState (action before)).construction.events
      (Goose.Proofs.Exit.stepState (protectDestination origin destination action before)).construction.events := by
  cases result : action before with
  | ok value state => simp [protectDestination, result, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | stop reason state => simp [protectDestination, result, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | escape target carriers state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have cleaned := preservesConstructionInvariant_cleanupReceivingDestination
        (predicate := PrefixInvariant state.construction.events) origin destination carriers state List.prefix_rfl
      cases cleanup : cleanupReceivingDestination origin destination carriers state <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using cleaned
  | jump target kind state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      cases kind with
      | breakValue carriers =>
          have cleaned := preservesConstructionInvariant_cleanupReceivingDestination
            (predicate := PrefixInvariant state.construction.events) origin destination carriers state List.prefix_rfl
          cases cleanup : cleanupReceivingDestination origin destination carriers state <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using cleaned
      | continueLoop =>
          have cleaned := preservesConstructionInvariant_cleanupReceivingDestination
            (predicate := PrefixInvariant state.construction.events) origin destination [] state List.prefix_rfl
          cases cleanup : cleanupReceivingDestination origin destination [] state <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using cleaned

def nonfixedFillContinuation (fuel : Nat) (config : EvalConfig) (current : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) : EvalM Unit := do
  let source ← completedReceivingDestination source
  for _ in [0:count] do
    repeatElement fuel config.layout current element source origin
  receivingAction origin current (fun destination => retireRepeatedSource destination source)
  receivingAction origin current finishDestination

theorem nonfixedFillContinuation_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (current : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (nonfixedFillContinuation fuel config current element count source origin) := by
  intro before
  apply (eventPrefix_iff_isPrefix _ _).mpr
  have preserved : PreservesConstructionInvariant (PrefixInvariant before.construction.events)
      (nonfixedFillContinuation fuel config current element count source origin) := by
    unfold nonfixedFillContinuation
    apply preservesConstructionInvariant_bind
    · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination source)
    · intro completed
      apply preservesConstructionInvariant_bind
      · apply preservesConstructionInvariant_rangeForIn
        intro index currentValue
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_repeatElement fuel config.layout current element completed origin
        · intro _; exact preservesConstructionInvariant_pure _
      · intro _
        apply preservesConstructionInvariant_bind
        · kernel_protocol
        · intro _; kernel_protocol
  exact preserved before List.prefix_rfl

theorem nonfixedFill_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming current source : Goose.Core.DestinationId) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (initial ready sourceReady : ExecutionState)
    (nonfixed : element.nonfixed = true)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current ready)
    (allocated : newDestination config.layout environment.act element .value origin none none ready = .ok source sourceReady) :
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment source operand sourceReady)).construction.events
      (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) initial)).construction.events := by
  let action : EvalM Unit := do
    let source ← newDestination config.layout environment.act element .value origin
    buildExpr fuel config environment source operand
    nonfixedFillContinuation fuel config current element count source origin
  have execution : buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) initial =
      protectDestination origin current action ready := by
    rw [nonfixedElementFill_execution fuel config environment incoming current element count operand origin initial ready nonfixed renewed]
    rfl
  have actionPrefix : EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment source operand sourceReady)).construction.events
      (Goose.Proofs.Exit.stepState (action ready)).construction.events := by
    simp only [action, bind, allocated]
    cases child : buildExpr fuel config environment source operand sourceReady with
    | ok unit state =>
        cases unit
        simpa [child, Goose.Proofs.Exit.stepState] using
          (nonfixedFillContinuation_keepsEventPrefix fuel config current element count source origin state)
    | stop | escape | jump => simp [child, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  rw [execution]
  exact eventPrefix_trans _ _ _ actionPrefix (protectedResult_sourcePrefix origin current action ready)

theorem nonfixedFill_repetitionReplay (fuel : Nat) (config : EvalConfig) (current : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    ∃ outcome visits,
      OperandReplay (fun _ : Nat => repeatElement fuel config.layout current element source origin)
        0 (List.range' 0 count 1) [] before outcome visits ∧
      visits.map Invocation.operand = (List.range' 0 count 1).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      (forIn [0:count] PUnit.unit fun _ _ => do
        repeatElement fuel config.layout current element source origin
        pure (.yield PUnit.unit)) before = discardValues outcome := by
  obtain ⟨outcome, visits, replay, loop, ordered, once⟩ := initializerLoop_replay
    (fun _ : Nat => repeatElement fuel config.layout current element source origin) (List.range' 0 count 1) before
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using loop

#print axioms nonfixedFill_repetitionReplay
def nonfixedFillAfterRepetition (current source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    ExecutionStep (List Unit) → ExecutionStep Unit
  | .ok _ state => (do
      receivingAction origin current (fun destination => retireRepeatedSource destination source)
      receivingAction origin current finishDestination) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem nonfixedFill_reachedSource_replay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming current source completed : Goose.Core.DestinationId) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (initial ready sourceReady builtReady repeatReady : ExecutionState)
    (nonfixed : element.nonfixed = true)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) initial = .ok current ready)
    (allocated : newDestination config.layout environment.act element .value origin none none ready = .ok source sourceReady)
    (built : buildExpr fuel config environment source operand sourceReady = .ok () builtReady)
    (completedResult : completedReceivingDestination source builtReady = .ok completed repeatReady) :
    ∃ outcome visits,
      OperandReplay (fun _ : Nat => repeatElement fuel config.layout current element completed origin)
        0 (List.range' 0 count 1) [] repeatReady outcome visits ∧
      visits.map Invocation.operand = (List.range' 0 count 1).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) initial =
        protectDestination origin current (fun _ => nonfixedFillAfterRepetition current completed origin outcome) ready := by
  obtain ⟨outcome, visits, replay, ordered, once, loop⟩ :=
    nonfixedFill_repetitionReplay fuel config current element count completed origin repeatReady
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  rw [nonfixedElementFill_execution fuel config environment incoming current element count operand origin initial ready nonfixed renewed]
  have bodyEq : (do
      let source ← newDestination config.layout environment.act element .value origin
      buildExpr fuel config environment source operand
      let source ← completedReceivingDestination source
      for _ in [0:count] do
        repeatElement fuel config.layout current element source origin
      receivingAction origin current (fun destination => retireRepeatedSource destination source)
      receivingAction origin current finishDestination) ready = nonfixedFillAfterRepetition current completed origin outcome := by
    simp only [bind, allocated, built, completedResult]
    simp only [bind] at loop
    rw [loop]
    cases outcome <;> rfl
  simp only [protectDestination, bodyEq]

#print axioms nonfixedFill_reachedSource_replay
theorem nonfixedFill_declaration_sourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current source : Goose.Core.DestinationId)
    (element : Ty) (count : Nat) (operand : Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial ready sourceReady : ExecutionState) (nonfixed : element.nonfixed = true)
    (occurrence : DeclarationOccurrence (fuel + 1) config environment localVar
      (.fill (.arr element count) operand expressionOrigin) origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current ready)
    (allocated : newDestination config.layout environment.act element .value expressionOrigin none none ready = .ok source sourceReady)
    (supported : FuelSupport config fuel (.builder environment source operand)) :
    SourceHistory config fuel ((path ++ [0]) ++ [0]) (.builder environment source operand) sourceReady
      (buildExpr fuel config environment source operand sourceReady) ∧
    buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand expressionOrigin) initial =
      protectDestination expressionOrigin current (do
        let source ← newDestination config.layout environment.act element .value expressionOrigin
        buildExpr fuel config environment source operand
        nonfixedFillContinuation fuel config current element count source expressionOrigin) ready ∧
    ∃ sourceEvents continuation : List Goose.Core.ConstructionEvent,
      (Goose.Proofs.Exit.stepState (buildExpr fuel config environment source operand sourceReady)).construction.events =
        sourceReady.construction.events ++ sourceEvents ∧
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 2) config environment
        (.letS localVar (.fill (.arr element count) operand expressionOrigin) origin) before)).construction.events =
          sourceReady.construction.events ++ sourceEvents ++ continuation := by
  have sourcePrefix := (evaluation_keepsEventPrefix fuel config).build environment source operand sourceReady
  have fillPrefix := nonfixedFill_sourcePrefix fuel config environment incoming current source element count operand
    expressionOrigin initial ready sourceReady nonfixed renewed allocated
  have declarationPrefix := DeclarationOccurrence.sourcePrefix occurrence
  have remaining := eventPrefix_trans _ _ _ fillPrefix declarationPrefix
  obtain ⟨sourceEvents, sourceEq⟩ := sourcePrefix
  obtain ⟨continuation, finalEq⟩ := remaining
  have execution := nonfixedElementFill_execution fuel config environment incoming current element count operand
    expressionOrigin initial ready nonfixed renewed
  refine ⟨fuelHistory_exists fuel config _ _ sourceReady supported, ?_, sourceEvents, continuation, sourceEq, ?_⟩
  · exact execution
  rw [finalEq, sourceEq]

#print axioms nonfixedFill_declaration_sourceEvents
#print axioms nonfixedFill_sourcePrefix
#print axioms nonfixedFillContinuation_keepsEventPrefix
#print axioms protectedResult_sourcePrefix
end Goose.Proofs.ConstructionGhostProtectedSourceEvents
