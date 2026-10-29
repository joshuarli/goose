import Goose.Proofs.ConstructionAcceptedByteReturnComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem withCompletion_byteReceiver_separated_timeouts (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant before.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (current : destinationCurrent before.construction id = .ok id) :
    let final := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } }
    withCompletionChannels [.construct id] origin
      (fun channels => evalProduce 0 config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before = .stop .timeout final ∧
    withCompletionChannels [.construct id] origin
      (fun channels => evalProduce 1 config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before = .stop .timeout final ∧
    AcceptedWorld config initialized final (.returned [] :: ambient) types live regions [] := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let activated := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  let final := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push .released } }
  have activatedWorld : AcceptedWorld config initialized activated (.exitChannels [token] [] [] :: ambient) types live regions [] :=
    direct_fresh_acceptedWorld_separated config initialized before ambient types live regions id ready.destination [] world history ready.present ready.opened current separated
  have activeTicket : activated.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by simp [activated, token]
  obtain ⟨after, cleanup, afterWorld⟩ := exit_cleanup_accepted_world config initialized activated token id id ready.destination [] []
    ambient types live regions [] origin activeTicket activatedWorld (by intro frame member; cases member)
  have activeRelease := releaseExitReservation_active activated.construction token .fresh id id ready.destination activeTicket
  have finalCleanup : exitChannelCleanupBorrowed origin [] [token] false [] activated = .ok () final := by
    simp [exitChannelCleanupBorrowed, List.forIn_cons, List.forIn_nil, liftConstruction, activeRelease,
      bind, pure, final, activated, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push]
  have same : after = final := (ExecutionStep.ok.inj (cleanup.symm.trans finalCleanup)).2
  subst after
  have setup : completionChannelSetup [.construct id] origin before = .ok ([.completion token], [token]) waited := by
    simp [completionChannelSetup, waitExitDestination, token, waited, liftConstruction, ConstructionM.get, ConstructionM.set, bind, pure]
  have selected := (wait_then_select_completion_open_byte before environment id ready.destination (.varr (.int .u8)) bytes origin
    ready.present ready.opened current).2
  have selected' : selectCompletionChannel environment (.bytes (.varr (.int .u8)) bytes origin) (.completion token) waited =
      .ok (.construct id) activated := by
    simpa [token, waited, activated, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push] using selected
  have waitingRelease : releaseExitReservation token waited.construction = .ok () final.construction := by
    simp [releaseExitReservation, ConstructionM.get, ConstructionM.set, bind, token, waited, final,
      Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push]
  have activeRelease' : releaseExitReservation token activated.construction = .ok () final.construction := by
    simpa [activated, final, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push] using activeRelease
  refine ⟨?_, ?_, afterWorld⟩
  · simp [withCompletionChannels, setup, evalProduce, Goose.Construct.timeout, EvalM.stop,
      List.forIn_cons, List.forIn_nil, liftConstruction, waitingRelease, bind, pure, waited, final]
  · simp only [withCompletionChannels, setup, evalProduce, List.mapM_cons, List.mapM_nil, bind, pure, selected']
    simp [buildExpr, Goose.Construct.timeout, EvalM.stop, List.forIn_cons, List.forIn_nil,
      liftConstruction, activeRelease', bind, pure, activated, final]

theorem withCompletion_byteReceiver_timeouts (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (current : destinationCurrent before.construction id = .ok id) :
    let final := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } }
    withCompletionChannels [.construct id] origin
      (fun channels => evalProduce 0 config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before = .stop .timeout final ∧
    withCompletionChannels [.construct id] origin
      (fun channels => evalProduce 1 config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before = .stop .timeout final ∧
    AcceptedWorld config initialized final (.returned [] :: ambient) types live regions [] := by
  apply withCompletion_byteReceiver_separated_timeouts config initialized environment id bytes origin before ambient types live regions world history ?_ ready current
  intro retained member
  rw [noRetained] at member
  cases member

#print axioms withCompletion_byteReceiver_separated_timeouts
#print axioms withCompletion_byteReceiver_timeouts
end Goose.Proofs.ConstructionAcceptedExecution
