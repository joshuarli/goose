import Goose.Proofs.ConstructionAcceptedRegisterCallWorld
import Goose.Proofs.ConstructionAcceptedScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem FutureGlobalsClear.releaseScope {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    (clear : FutureGlobalsClear config initialized state) (environment : RuntimeActivation) (scope scopeInst : Nat) :
    FutureGlobalsClear config initialized (releaseScopeState environment scope scopeInst state) := by
  intro id future inside
  have outside : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains (.global id) = false := by
    apply Bool.eq_false_iff.mpr
    intro contains
    have member := List.contains_iff_mem.mp contains
    simp only [Goose.Proofs.Exit.runtimeScopeRoots, List.mem_filterMap] at member
    obtain ⟨entry, _, found⟩ := member
    split at found <;> simp_all
  exact ⟨(Goose.Proofs.ExitExecution.releaseScopeState_root_lookup environment scope scopeInst state (.global id) outside).trans
      (clear id future inside).1,
    (releaseScopeState_ordinal_lookup environment scope scopeInst state (.global id) outside).trans
      (clear id future inside).2⟩

theorem withScope_normal_prefix (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (scope scopeInst : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (action : EvalM α)
    (before after : ExecutionState) (result : α) (evaluated : action before = .ok result after)
    (world : AcceptedWorld config initialized after ambient types live regions pending)
    (clear : FutureGlobalsClear config initialized after) :
    let final := releaseScopeState environment scope scopeInst after
    withScope environment scope scopeInst action before = .ok result final ∧
      AcceptedWorld config initialized final ambient types
        (fun root => live root ∧ (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false)
        regions pending ∧ FutureGlobalsClear config initialized final := by
  exact ⟨by simp [withScope, evaluated, releaseScope, bind, EvalM.get, EvalM.set],
    world.releaseScope config initialized after ambient types live regions pending environment scope scopeInst,
    clear.releaseScope environment scope scopeInst⟩

theorem withScope_stopped_prefix (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (scope scopeInst : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (action : EvalM α)
    (before after : ExecutionState) (reason : Goose.Core.Stop) (evaluated : action before = .stop reason after)
    (world : AcceptedWorld config initialized after ambient types live regions pending)
    (clear : FutureGlobalsClear config initialized after) :
    withScope environment scope scopeInst action before = .stop reason after ∧
      AcceptedWorld config initialized after ambient types live regions pending ∧ FutureGlobalsClear config initialized after := by
  exact ⟨by simp [withScope, evaluated], world, clear⟩

#print axioms FutureGlobalsClear.releaseScope
#print axioms withScope_normal_prefix
#print axioms withScope_stopped_prefix
end Goose.Proofs.ConstructionAcceptedExecution
