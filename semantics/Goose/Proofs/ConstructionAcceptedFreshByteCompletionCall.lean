import Goose.Proofs.ConstructionAcceptedFreshByteBuiltCall
import Goose.Proofs.ConstructionExitFreshSeparation
import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ConstructionExitCompletionActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_call_completion_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id implId : Nat) (helper : Construct.Impl) (bytes : List UInt8)
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
    let producer := { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
    ∃ after, withCompletionChannels [.construct id] origin
      (fun channels => evalProduce (fuel + 2) config producer channels (.bytes (.varr (.int .u8)) bytes origin)) scopeState =
      .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: .callChannels activation [] :: ambient) types live
        (freshReceivingRegion before id :: regions) (⟨[.construct id], [.completed id]⟩ :: pending) := by
  let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
  let scopeState := ownershipResultScopeState activation scope pushed
  let producer := { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
  let token := scopeState.construction.exitReservations.size
  let waited := { scopeState with construction := { scopeState.construction with
    exitReservations := scopeState.construction.exitReservations.push (.waiting id) } }
  let prepared := { scopeState with construction := { scopeState.construction with
    exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have bounded := retained_destination_bounds config initialized before ambient types live regions pending world coverage
  have prep := fresh_byte_call_prepared_world_bounded config initialized caller scope allocationOrigin knownCount before allocated id
    activation ambient types live regions pending world created rfl rfl ready coverage.1 bounded
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  have preparedCurrent : destinationCurrent prepared.construction id = .ok id := by
    rw [destinationCurrent_congr_tables allocated.construction prepared.construction rfl rfl id]
    exact current
  obtain ⟨row, found, packed, request, direct, receiver, adaptation, physical⟩ :=
    newDestination_byteOwner_packed_value_with_physical config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : row = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst row
  obtain ⟨built, produced, builtWorld, actualBuild⟩ := fresh_byte_call_produce_observed_world fuel config initialized caller scope
    allocationOrigin origin knownCount before allocated id implId helper bytes ambient types live regions pending world coverage created ready fits
  have tickets := buildExpr_bytes_tickets fuel config producer id (.varr (.int .u8)) bytes origin prepared built
    ready.destination 0 prep.1.ownership.source preparedCurrent preparedReady.present preparedReady.opened actualBuild
  have ticket : built.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    simp [prepared, token]
  obtain ⟨backed, ⟨landing⟩, landed⟩ := accepted_byte_receiver_landing_ready fuel config initialized producer bytes origin id 0
    prepared built (.exitChannels [token] [] [.completed id] :: .callChannels activation [] :: ambient) types live
    (freshReceivingRegion before id :: regions) pending prep.1 preparedReady packed request receiver (by simpa using fits) preparedCurrent actualBuild
  have targetReady : CarriersLandingReady built [.construct id] [.completed id] := by
    refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .construct id id landing
  have targetBacked : ∀ carrier ∈ [.completed id], CarrierResultBacking config.layout built carrier := by
    intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact backed
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have separate : ∀ pendingFrame ∈ pending, .completion token ∉ pendingFrame.channels := by
    simpa only [token, scopeState, ownershipResultScopeState, pushed, frame.tickets] using
      acceptedWorld_fresh_pending_separate config initialized before ambient types live regions pending world
  obtain ⟨after, cleanup, afterWorld⟩ := exit_cleanup_returned_world config initialized built token id id ready.destination []
    [.construct id] [.completed id] (.callChannels activation [] :: ambient) types live (freshReceivingRegion before id :: regions)
    pending origin ticket builtWorld separate (by simp) targetReady targetBacked
  have selection := wait_then_select_completion_open_byte scopeState producer id ready.destination (.varr (.int .u8)) bytes origin
    ready.present ready.opened current
  have selected : selectCompletionChannel producer (.bytes (.varr (.int .u8)) bytes origin) (.completion token) waited =
      .ok (.construct id) prepared := by
    simpa [token, waited, prepared, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push] using selection.2
  have renewal : renewReceivingDestination id prepared.construction = .ok id prepared.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, preparedCurrent, pure,
      lookupDestination_result, preparedReady.present, preparedReady.opened]
  have action : evalProduce (fuel + 2) config producer [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
      evalProduce (fuel + 2) config producer [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared := by
    simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure, selected]
    simp [selectCompletionChannel, pure]
  have producedCompletion : evalProduce (fuel + 2) config producer [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
      .ok [.completed id] built := action.trans produced
  have setup : completionChannelSetup [.construct id] origin scopeState = .ok ([.completion token], [token]) waited := by
    simp [completionChannelSetup, waitExitDestination, token, waited, liftConstruction, ConstructionM.get, ConstructionM.set, bind, pure]
  let final := { built with construction := { built.construction with
    exitReservations := built.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active built.construction token .fresh id id ready.destination ticket
  have actualCleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed id] built = .ok () final := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have equal : after = final := (ExecutionStep.ok.inj (cleanup.symm.trans actualCleanup)).2
  subst after
  refine ⟨final, ?_, afterWorld⟩
  change withCompletionChannels [.construct id] origin (fun channels => evalProduce (fuel + 2) config producer channels (.bytes (.varr (.int .u8)) bytes origin)) scopeState = .ok [.completed id] final
  simp [withCompletionChannels, setup, producedCompletion, materializeOwnedCarriers, List.mapM_cons, List.mapM_nil,
    List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure, final]

#print axioms fresh_byte_call_completion_world
end Goose.Proofs.ConstructionAcceptedExecution
