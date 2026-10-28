import Goose.Proofs.ConstructionEmptyHelperCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem acceptedEntry_callIdentity (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (entry : RuntimeActivation) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state [.callChannels entry []] types live regions pending) :
    state.activations.length < Goose.Core.maxCallDepth ∧
    OwnershipAmbient.withoutActivation state.nextAct [.callChannels entry []] = [.callChannels entry []] := by
  have frames := world.ownership.runtime.activations
  simp only [OwnershipAmbient.activations, List.filterMap_cons, OwnershipAmbientFrame.activationChannels,
    List.filterMap_nil] at frames
  have count := congrArg List.length frames
  simp only [List.length_map, List.length_cons, List.length_nil] at count
  have depth : state.activations.length < Goose.Core.maxCallDepth := by
    rw [count]
    decide
  cases active : state.activations with
  | nil => simp [active] at count
  | cons head tail =>
    have one : tail = [] := by simpa [active] using count
    subst tail
    simp only [active, List.map_cons, List.map_nil, List.cons.injEq] at frames
    have identifier : head.act = entry.act := congrArg OwnershipActivationChannels.act frames.1
    have bounded := world.ownership.identities.activations.2 head (by simp [active])
    rw [identifier] at bounded
    have different : entry.act ≠ state.nextAct := Nat.ne_of_lt bounded
    refine ⟨by simpa only [active] using depth, ?_⟩
    simp [OwnershipAmbient.withoutActivation, different]

#print axioms acceptedEntry_callIdentity
end Goose.Proofs.ConstructionAcceptedExecution
