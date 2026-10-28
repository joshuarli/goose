import Goose.Proofs.ConstructionByteValueStopped
import Goose.Proofs.ConstructionByteStorageFrame

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_byteOwner_stopped_split (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before after : ExecutionState) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (stop : Goose.Core.Stop) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (executed : evalValue fuel config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .stop stop after) :
    (after = before ∧ AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types) ∨
    (after = reserveByteStorage before ∧ OwnershipSourceState after.construction ∧ AcceptedFrame config accepted frame after types) ∨
    ∃ destination, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before destination :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, ExecutionStep.stop.injEq] at executed
    obtain ⟨_, same⟩ := executed
    subst after
    exact Or.inl ⟨rfl, world, source⟩
  | succ fuel =>
    cases created : newDestination config.layout frame.interpretation.environment.act (.varr (.int .u8)) .value origin none
        (some bytes.length) before with
    | stop reason final =>
      have created' := created
      simp only [EvalConfig.layout] at created'
      simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created',
        ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      have same := newDestination_byteOwner_stopped_state config.layout frame.interpretation.environment.act origin bytes.length
        before final reason created
      have valid := (newDestination_byteOwner_stopped_source config.layout frame.interpretation.environment.act origin bytes.length
        before final reason world.ownership.source created).1
      have kept := newDestination_byteOwner_stopped_frame frame.interpretation.environment.act origin bytes.length reason source created
      exact Or.inr (Or.inl ⟨by simpa only [reserveByteStorage] using same, valid, kept⟩)
    | escape address carriers final =>
      have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | jump target kind final =>
      have localAction := newByteDestination_local config frame.interpretation.environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | ok destination allocated =>
      cases fuel with
      | zero =>
        have created' := created
        simp only [EvalConfig.layout] at created'
        simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created',
          buildExpr, timeout, EvalM.stop, ExecutionStep.stop.injEq] at executed
        obtain ⟨rfl, rfl⟩ := executed
        exact Or.inr (Or.inr (evalValue_byteOwner_timeout_world config accepted frame before allocated bytes origin
          ambient types live regions pending world source (by
            simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte,
              created', buildExpr, timeout, EvalM.stop])))
      | succ fuel =>
        exact Or.inr (Or.inr ⟨destination, evalValue_byteOwner_stopped_afterAllocation fuel config accepted frame before allocated after
          bytes origin destination stop ambient types live regions pending world source created executed⟩)

#print axioms evalValue_byteOwner_stopped_split

end Goose.Proofs.ConstructionAcceptedExecution
