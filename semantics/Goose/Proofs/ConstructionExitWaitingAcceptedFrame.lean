import Goose.Proofs.ConstructionAcceptedByteChecked
import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCompletion

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedFrame_waitExitDestination {config : EvalConfig} {accepted : AcceptedModule config}
    {source : ConstructionSourceFrame} {before : ExecutionState} {types : RootTypes}
    (id : Nat) (valid : AcceptedFrame config accepted source before types) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    waitExitDestination id before.construction = .ok before.construction.exitReservations.size waited.construction ∧
    AcceptedFrame config accepted source waited types := by
  let after := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have outer : after = { before with construction := after.construction } := rfl
  refine ⟨?_, ?_⟩
  · simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure, after]
  ·
    have objects := congrArg ExecutionState.objects outer
    have ordinals := congrArg ExecutionState.objectOrdinals outer
    have acts := congrArg ExecutionState.nextAct outer
    have scopes := congrArg ExecutionState.nextScope outer
    refine ⟨valid.compatible, ?_, ?_, valid.initializingBefore, valid.aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [acts] using valid.frontier
    · simpa only [scopes] using valid.scopeFrontier
    · intro var member
      obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := valid.locals var member
      exact ⟨descriptor, root, value, declared, rootOf_transfer source.interpretation var before after root resolved,
        by rw [objects]; exact found, represented⟩
    · intro var member descriptor root declared resolved
      exact valid.localTypes var member descriptor root declared
        (rootOf_transfer source.interpretation var after before root resolved)
    · intro var uninitialized root resolved
      obtain ⟨absent, ordinal⟩ := valid.uninitializedLocals var uninitialized root
        (rootOf_transfer source.interpretation var after before root resolved)
      exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
    · intro var uninitialized root resolved
      exact valid.uninitializedTypes var uninitialized root
        (rootOf_transfer source.interpretation var after before root resolved)
    · intro global future within
      obtain ⟨absent, ordinal⟩ := valid.futureGlobals global future within
      exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
    · intro var member root value resolved found
      exact valid.direct var member root value (rootOf_transfer source.interpretation var after before root resolved)
        (by rw [objects] at found; exact found)
    · intro fuel var member roots annotated root location value resolved found read interior reference
      have prior := rootOf_transfer source.interpretation var after before root resolved
      have oldFound : before.objects.lookup root = some (.ref location) := by rw [objects] at found; exact found
      have priorRead := readLoc_directReference_transfer fuel config.layout location after before value interior
        (by rw [objects]) read reference
      exact valid.contents fuel var member roots annotated root location value prior oldFound priorRead interior reference

theorem checked_completion_byte_history (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (world : AcceptedWorld config source.initialized before ambient types live regions pending)
    (frame : AcceptedFrame config accepted source before types)
    (history : EvaluationHistoryCoverage before ambient pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let result : PendingCarrierFrame := ⟨[.completion token], [.completed id]⟩
    waitExitDestination id before.construction = .ok token waited.construction ∧
    AcceptedFrame config accepted source waited types ∧
    ∃ after, evalProduce (fuel + 2) config source.interpretation.environment result.channels
      (.bytes (.varr (.int .u8)) bytes origin) waited = .ok result.carriers after ∧
      EvaluationHistoryCoverage after (.returned result.carriers :: .completionChannels [token] [] [] :: ambient)
        (result :: pending) ∧
      CarriersLandingReady after result.channels result.carriers ∧
      (∀ carrier ∈ result.carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin result.channels result.carriers after = .ok () after := by
  have waited := acceptedFrame_waitExitDestination id frame
  obtain ⟨after, _, evaluated, tracked, readyAfter, backed, landed⟩ :=
    completion_byte_receiver_history fuel config source.initialized source.interpretation.environment before ambient types
      live regions pending id bytes origin world history ready receiver packed adaptation request current fits
  exact ⟨waited.1, waited.2, after, evaluated, tracked, readyAfter, backed, landed⟩

#print axioms checked_completion_byte_history

#print axioms acceptedFrame_waitExitDestination

end Goose.Proofs.ConstructionAcceptedExecution
