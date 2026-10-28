import Goose.Proofs.ConstructionGhostProtectedSourceEvents

namespace Goose.Proofs.ConstructionGhostBuilderCallEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostProtectedSourceEvents

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def builderCallSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.DestinationId × Goose.Core.ContextId × List Arg × Goose.Core.OriginId)
  | .builder environment destination (.call context arguments origin) => some (environment, destination, context, arguments, origin)
  | _ => none

theorem builderCall_child_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (incoming destination : Goose.Core.DestinationId)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : builderCallSyntax operation = some (environment, incoming, context, arguments, origin))
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready) :
    SourceHistory config sourceFuel (path ++ [0]) (.channelCall environment context arguments [.construct destination] origin) ready
      (invokeCall sourceFuel config environment context arguments [.construct destination] origin ready) := by
  cases history <;> simp_all [builderCallSyntax]
  case scalarBuilder =>
    rename_i scalar child
    cases scalar <;> simp_all [builderCallSyntax]
  case supportedBuilder =>
    rename_i supported valueChild builderChild
    cases supported <;> simp_all [builderCallSyntax]

#print axioms builderCall_child_history

def builderCallContinuation (destination : Goose.Core.DestinationId) : ExecutionStep (List Carrier) → ExecutionStep Unit
  | .ok carriers state => (do
      let .completed actual ← singleCarrier carriers | fault .shape
      let original ← getDestination (← receivingDestination destination)
      let actual ← getDestination actual
      if actual.storage != original.storage then fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem builderCallContinuation_sourcePrefix (destination : Goose.Core.DestinationId) (outcome : ExecutionStep (List Carrier)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (builderCallContinuation destination outcome)).construction.events := by
  cases outcome with
  | ok carriers state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let .completed actual ← singleCarrier carriers | fault .shape
              let original ← getDestination (← receivingDestination destination)
              let actual ← getDestination actual
              if actual.storage != original.storage then fault .flow) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_singleCarrier carriers)
        · intro carrier
          cases carrier with
          | register | pendingNamed => exact preservesConstructionInvariant_fault _
          | completed actual =>
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingDestination destination)
              · intro current
                apply preservesConstructionInvariant_bind
                · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination current)
                · intro original
                  apply preservesConstructionInvariant_bind
                  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination actual)
                  · intro actualDestination
                    split <;> first | exact preservesConstructionInvariant_fault _ | exact preservesConstructionInvariant_pure _
      simpa [builderCallContinuation, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using preserved state List.prefix_rfl
  | stop | escape | jump => exact eventPrefix_refl _

theorem builderCall_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming destination : Goose.Core.DestinationId) (context : Goose.Core.ContextId) (arguments : List Arg)
    (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (invokeCall fuel config environment context arguments [.construct destination] origin ready)).construction.events
      (Goose.Proofs.Exit.stepState (buildExpr (fuel + 1) config environment incoming (.call context arguments origin) before)).construction.events := by
  let action : EvalM Unit := fun _ => builderCallContinuation destination
    (invokeCall fuel config environment context arguments [.construct destination] origin ready)
  have execution : buildExpr (fuel + 1) config environment incoming (.call context arguments origin) before =
      protectDestination origin destination action ready := by
    simp only [buildExpr, expressionOrigin, bind, renewed, protectDestination, action, builderCallContinuation]
    cases invokeCall fuel config environment context arguments [.construct destination] origin ready <;> rfl
  rw [execution]
  have afterProtect := protectedResult_sourcePrefix origin destination action ready
  exact eventPrefix_trans _ _ _ (builderCallContinuation_sourcePrefix destination _) afterProtect

#print axioms builderCallContinuation_sourcePrefix
#print axioms builderCall_sourcePrefix
end Goose.Proofs.ConstructionGhostBuilderCallEvents
