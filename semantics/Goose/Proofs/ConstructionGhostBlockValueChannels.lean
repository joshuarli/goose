import Goose.Proofs.ConstructionGhostActivationResultEvents

namespace Goose.Proofs.ConstructionGhostBlockValueChannels
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem blockValue_afterChannels (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before ready : ExecutionState) (types : List Ty) (channels : List Channel)
    (typesFound : blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels ready) :
    evalValue (fuel + 1) config environment (.blockE block origin) before =
      (do let carriers ← evalProduce fuel config environment channels (.blockE block origin)
          publishCarriers origin carriers
          carrierValue (← singleCarrier carriers)) ready := by
  simp only [evalValue, typesFound, bind, prepared]

theorem blockValue_producerPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before ready : ExecutionState) (types : List Ty) (channels : List Channel)
    (typesFound : blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalProduce fuel config environment channels (.blockE block origin) ready)).construction.events
      (Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config environment (.blockE block origin) before)).construction.events := by
  rw [blockValue_afterChannels fuel config environment block origin before ready types channels typesFound prepared]
  simp only [bind]
  cases result : evalProduce fuel config environment channels (.blockE block origin) ready with
  | ok carriers state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do publishCarriers origin carriers; carrierValue (← singleCarrier carriers)) := by
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_publishCarriers _ _
        · intro ignored
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_singleCarrier carriers)
          · intro carrier
            exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue carrier)
      simpa [result, bind, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
  | stop | escape | jump => simp [result, Goose.Proofs.Exit.stepState, eventPrefix_refl]

#print axioms blockValue_afterChannels
#print axioms blockValue_producerPrefix
end Goose.Proofs.ConstructionGhostBlockValueChannels
