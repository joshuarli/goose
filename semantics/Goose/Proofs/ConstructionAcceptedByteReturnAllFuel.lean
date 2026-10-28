import Goose.Proofs.ConstructionAcceptedByteReturnTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem withCompletion_byteReceiver_allFuel (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    let outcome := withCompletionChannels [.construct id] origin
      (fun channels => evalProduce fuel config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before
    ∃ carriers pending,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) (.returned carriers :: ambient) types live regions pending ∧
      (match outcome with
      | .ok actual _ => actual = [.completed id] ∧ carriers = actual ∧ pending = [⟨[.construct id], [.completed id]⟩]
      | .stop .. => carriers = [] ∧ pending = []
      | _ => False) := by
  cases fuel with
  | zero =>
    have timed := withCompletion_byteReceiver_timeouts config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready current
    refine ⟨[], [], ?_⟩
    simpa only [timed.1, Goose.Proofs.Exit.stepState] using And.intro timed.2.2 (And.intro (show ([] : List Goose.Construct.Carrier) = [] from rfl) (show ([] : List PendingCarrierFrame) = [] from rfl))
  | succ fuel =>
    cases fuel with
    | zero =>
      have timed := withCompletion_byteReceiver_timeouts config initialized environment id bytes origin before ambient types live regions
        world history noRetained ready current
      refine ⟨[], [], ?_⟩
      simpa only [timed.2.1, Goose.Proofs.Exit.stepState] using And.intro timed.2.2 (And.intro (show ([] : List Goose.Construct.Carrier) = [] from rfl) (show ([] : List PendingCarrierFrame) = [] from rfl))
    | succ fuel =>
      obtain ⟨after, produced, finalWorld⟩ := withCompletion_byteReceiver_world fuel config initialized environment id bytes origin
        before ambient types live regions world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
      refine ⟨[.completed id], [⟨[.construct id], [.completed id]⟩], ?_⟩
      simpa only [produced, Goose.Proofs.Exit.stepState, Nat.add_assoc] using And.intro finalWorld (And.intro (show [Goose.Construct.Carrier.completed id] = [Goose.Construct.Carrier.completed id] from rfl) (And.intro (show [Goose.Construct.Carrier.completed id] = [Goose.Construct.Carrier.completed id] from rfl) (show ([⟨[.construct id], [.completed id]⟩] : List PendingCarrierFrame) = [⟨[.construct id], [.completed id]⟩] from rfl)))

#print axioms withCompletion_byteReceiver_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
