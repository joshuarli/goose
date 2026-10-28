import Goose.Proofs.ConstructionGhostProtectedSourceEvents
import Goose.Proofs.ConstructionGhostInvocationEventChunks
import Goose.Proofs.ConstructionGhostInvocation

namespace Goose.Proofs.ConstructionGhostDeclarationArrayEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents
open Goose.Proofs.ConstructionGhostProtectedSourceEvents

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def arrayAfterElements (current : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) : ExecutionStep (List Unit) → ExecutionStep Unit
  | .ok _ state => receivingAction origin current finishDestination state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem arrayAfterElements_sourcePrefix (current : Goose.Core.DestinationId) (origin : Goose.Core.OriginId)
    (outcome : ExecutionStep (List Unit)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (arrayAfterElements current origin outcome)).construction.events := by
  cases outcome with
  | ok values state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (receivingAction origin current finishDestination) := by kernel_protocol
      exact preserved state List.prefix_rfl
  | stop | escape | jump => exact eventPrefix_refl _

theorem array_declaration_sourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (occurrence : DeclarationOccurrence (fuel + 1) config environment localVar (.arrLit ty operands expressionOrigin)
      origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element)
    (supported : ∀ operand ∈ operands, FuelSupport config fuel (.element environment current element operand)) :
    ∃ outcome visits chunks continuation,
      OperandReplay (fun operand => buildElement fuel config environment current element operand) 0 operands [] ready outcome visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel ((path ++ [0]) ++ [visit.ordinal])
        (.element environment current element visit.operand) visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 2) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events =
        ready.construction.events ++ chunks.flatten ++ continuation := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    arrayLiteral_execution_replay fuel config environment incoming current ty operands expressionOrigin initial prepared ready pending element renewed found elementFound
  obtain ⟨chunks, aligned, chunksEq, _, _⟩ := replay_eventChunks replay
    (fun operand => (evaluation_keepsEventPrefix fuel config).element environment current element operand)
  have finishPrefix := arrayAfterElements_sourcePrefix current expressionOrigin outcome
  let action : EvalM Unit := fun _ => arrayAfterElements current expressionOrigin outcome
  have protectPrefix := protectedResult_sourcePrefix expressionOrigin current action prepared
  have declarationPrefix := DeclarationOccurrence.sourcePrefix occurrence
  have actionEq : (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment incoming
      (.arrLit ty operands expressionOrigin) initial)).construction.events =
      (Goose.Proofs.Exit.stepState (protectDestination expressionOrigin current action prepared)).construction.events := by
    rw [execution]
    cases outcome <;> rfl
  change EventPrefix (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment incoming
    (.arrLit ty operands expressionOrigin) initial)).construction.events
    (Goose.Proofs.Exit.stepState (execStmt (fuel + 2) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events at declarationPrefix
  rw [actionEq] at declarationPrefix
  have combined := eventPrefix_trans _ _ _ finishPrefix protectPrefix
  have combined := eventPrefix_trans _ _ _ combined declarationPrefix
  obtain ⟨continuation, finalEq⟩ := combined
  refine ⟨outcome, visits, chunks, continuation, replay, ?_, ordered, once, aligned, chunksEq, ?_⟩
  · intro visit member
    have inMapped : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
    rw [ordered] at inMapped
    have inOperands := List.mem_of_mem_take inMapped
    have child := fuelHistory_exists fuel config (.element environment current element visit.operand)
      ((path ++ [0]) ++ [visit.ordinal]) visit.before (supported visit.operand inOperands)
    simp only [execute] at child
    rw [← visit_executes replay visit member]
    exact child
  · rw [finalEq, chunksEq]

#print axioms array_declaration_sourceEvents
end Goose.Proofs.ConstructionGhostDeclarationArrayEvents
