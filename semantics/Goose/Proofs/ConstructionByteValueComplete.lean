import Goose.Proofs.ConstructionByteStorageWorld
import Goose.Proofs.ConstructionByteValueOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_byteOwner_stopped_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before after : ExecutionState) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (executed : evalValue fuel config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .stop stop after) :
    ∃ nextRegions, AcceptedWorld config frame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted frame after types := by
  rcases evalValue_byteOwner_stopped_split fuel config accepted frame before after bytes origin stop ambient types live regions pending
    world source executed with ⟨same, finalWorld, finalSource⟩ | ⟨same, _, finalSource⟩ | ⟨id, finalWorld, finalSource⟩
  · exact ⟨regions, finalWorld, finalSource⟩
  · subst after
    exact ⟨regions, reserveByteStorage_world config frame.initialized before ambient types live regions pending world, finalSource⟩
  · exact ⟨freshReceivingRegion before id :: regions, finalWorld, finalSource⟩

theorem evalValue_byteOwner_accepted_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) :
    ∃ nextRegions,
      let after := Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment
        (.bytes (.varr (.int .u8)) bytes origin) before)
      AcceptedWorld config frame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted frame after types := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨regions, world, source⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      cases created : newDestination config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
          (some bytes.length) before with
      | stop reason after =>
        have created' := created
        simp only [EvalConfig.layout] at created'
        have stopped : evalValue 1 config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
            .stop reason after := by
          simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created']
        simpa only [stopped, Goose.Proofs.Exit.stepState] using
          evalValue_byteOwner_stopped_world 1 config accepted frame before after bytes origin reason ambient types live regions pending world source stopped
      | ok id after =>
        have created' := created
        simp only [EvalConfig.layout] at created'
        have stopped : evalValue 1 config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
            .stop .timeout after := by
          simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created',
            buildExpr, timeout, EvalM.stop]
        simpa only [stopped, Goose.Proofs.Exit.stepState] using
          evalValue_byteOwner_stopped_world 1 config accepted frame before after bytes origin .timeout ambient types live regions pending world source stopped
      | escape address carriers after =>
        have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
        rw [created] at localAction
        cases localAction
      | jump target kind after =>
        have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
        rw [created] at localAction
        cases localAction
    | succ fuel =>
      cases executed : evalValue (fuel + 2) config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before with
      | stop reason after =>
        simpa only [Goose.Proofs.Exit.stepState] using
          evalValue_byteOwner_stopped_world (fuel + 2) config accepted frame before after bytes origin reason ambient types live regions pending world source executed
      | ok value after =>
        obtain ⟨finalWorld, ⟨finalFrame⟩, _⟩ := evalValue_byteOwner_world fuel config frame.initialized frame.interpretation.environment
          bytes origin before after value ambient types live regions pending world executed
        exact ⟨regions, finalWorld, finalFrame.acceptedFrame source⟩
      | escape address carriers after =>
        have localAction := evalValue_byteOwner_local fuel config frame.interpretation.environment bytes origin before
        rw [executed] at localAction
        cases localAction
      | jump target kind after =>
        have localAction := evalValue_byteOwner_local fuel config frame.interpretation.environment bytes origin before
        rw [executed] at localAction
        cases localAction

#print axioms evalValue_byteOwner_stopped_world
#print axioms evalValue_byteOwner_accepted_world

end Goose.Proofs.ConstructionAcceptedExecution
