import Goose.Proofs.ConstructionAcceptedFreshBytePreparation
import Goose.Proofs.ConstructionAcceptedByteReturnProduce

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_call_build_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated after : ExecutionState) (id implId : Nat) (helper : Impl) (bytes : List UInt8)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (fits : bytes.length < 2 ^ 32)
    (built : let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
      let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
      let scopeState := ownershipResultScopeState activation scope pushed
      let prepared := { scopeState with construction := { scopeState.construction with
        exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
      buildExpr (fuel + 1) config { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
        id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    AcceptedWorld config initialized after
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending := by
  let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
  let scopeState := ownershipResultScopeState activation scope pushed
  let prepared := { scopeState with construction := { scopeState.construction with
    exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  have bounded := retained_destination_bounds config initialized before ambient types live regions pending world coverage
  have prep := fresh_byte_call_prepared_world_bounded config initialized caller scope allocationOrigin knownCount before allocated id
    activation ambient types live regions pending world created rfl rfl ready coverage.1 bounded
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  obtain ⟨row, found, packed, request, direct, receiver⟩ :=
    newDestination_byteOwner_packed_value config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : row = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst row
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  apply fresh_byte_build_accepted_world fuel config initialized caller
    { activation with scopes := (scope, pushed.nextScope) :: activation.scopes } bytes allocationOrigin origin knownCount
    before allocated prepared after id (.active .fresh id id ready.destination) ambient
    (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
    types live regions pending (freshReceivingRegion before id) world prep.1 created rfl prep.2.1 prep.2.2
    preparedReady packed request fits rfl
  · intro root active
    exact ⟨freshReceivingRegion before id, by simp, by simp [freshReceivingRegion]⟩
  · rw [destinationCurrent_congr_tables allocated.construction prepared.construction rfl rfl id]
    exact current
  · exact built

theorem fresh_byte_call_produce_observed_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id implId : Nat) (helper : Impl) (bytes : List UInt8)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (fits : bytes.length < 2 ^ 32) :
    let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    let producer := { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
    ∃ after, evalProduce (fuel + 2) config producer [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared =
        .ok [.completed id] after ∧
      AcceptedWorld config initialized after
        (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
        types live (freshReceivingRegion before id :: regions) pending ∧
      buildExpr (fuel + 1) config producer id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after := by
  let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
  let scopeState := ownershipResultScopeState activation scope pushed
  let prepared := { scopeState with construction := { scopeState.construction with
    exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  let producer := { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
  have bounded := retained_destination_bounds config initialized before ambient types live regions pending world coverage
  have prep := fresh_byte_call_prepared_world_bounded config initialized caller scope allocationOrigin knownCount before allocated id
    activation ambient types live regions pending world created rfl rfl ready coverage.1 bounded
  have originalCurrent := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  have current : destinationCurrent prepared.construction id = .ok id := by
    rw [destinationCurrent_congr_tables allocated.construction prepared.construction rfl rfl id]
    exact originalCurrent
  obtain ⟨row, found, packed, request, direct, receiver, adaptation, physical⟩ :=
    newDestination_byteOwner_packed_value_with_physical config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : row = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst row
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config producer bytes origin prepared id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request current (by simpa using fits)
  have afterSource := buildExpr_bytes_sourceState fuel config producer id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 prep.1.ownership.source current ready.present ready.opened built
  obtain ⟨destination, storage, found, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config producer bytes origin id 0 prepared after preparedReady packed request
      (by simpa using fits) prep.1.ownership.source.structural.1.1.1 current built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction afterSource.inactiveKeys id destination found
    (0 + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have currentAfter : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have renewal : renewReceivingDestination id prepared.construction = .ok id prepared.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, preparedReady.present, preparedReady.opened]
  have completed : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentAfter,
      bind, completedDestination, getDestination, EvalM.get, found, progress, pure]
  refine ⟨after, ?_, fresh_byte_call_build_world fuel config initialized caller scope allocationOrigin origin knownCount
    before allocated after id implId helper bytes ambient types live regions pending world coverage created ready fits built, built⟩
  change evalProduce (fuel + 2) config producer [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok [.completed id] after
  simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
    selectCompletionChannel, built, completed]

theorem fresh_byte_call_produce_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id implId : Nat) (helper : Impl) (bytes : List UInt8)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (fits : bytes.length < 2 ^ 32) :
    let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    let producer := { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
    ∃ after, evalProduce (fuel + 2) config producer [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared =
        .ok [.completed id] after ∧
      AcceptedWorld config initialized after
        (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
        types live (freshReceivingRegion before id :: regions) pending := by
  obtain ⟨after, produced, afterWorld, built⟩ := fresh_byte_call_produce_observed_world fuel config initialized caller scope
    allocationOrigin origin knownCount before allocated id implId helper bytes ambient types live regions pending world coverage created ready fits
  exact ⟨after, produced, afterWorld⟩

#print axioms fresh_byte_call_produce_observed_world
#print axioms fresh_byte_call_produce_world
#print axioms fresh_byte_call_build_world
end Goose.Proofs.ConstructionAcceptedExecution
