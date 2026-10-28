import Goose.Proofs.ConstructionAcceptedLocalFreshness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedWorld.freshScope_localType {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    {ambient : OwnershipAmbient} {types : RootTypes} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types live regions pending) (act id : Nat) :
    types (.local act state.nextScope id) = none := by
  cases present : types (.local act state.nextScope id) with
  | none => rfl
  | some ty =>
    have bound := world.typeFrontier act state.nextScope id ty present
    exact (Nat.lt_irrefl _ bound.2).elim

theorem AcceptedWorld.enterScope_localType {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    {ambient : OwnershipAmbient} {types : RootTypes} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (interpretation : RootInterpretation) (scope id : Nat) (descriptor : LocalVar)
    (declared : interpretation.environment.vars[id]? = some descriptor) (localScope : descriptor.scope = scope) :
    rootOf (interpretation.enterScope scope state.nextScope).environment id
      { state with nextScope := state.nextScope + 1 } =
      .ok (.local interpretation.environment.act state.nextScope id) { state with nextScope := state.nextScope + 1 } ∧
      types (.local interpretation.environment.act state.nextScope id) = none :=
  ⟨(freshScope_localRoot interpretation scope id descriptor state declared localScope).2,
    world.freshScope_localType interpretation.environment.act id⟩

theorem AcceptedFrame.enterScope_uninitializedTypes {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame state types)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending) (scope : Nat)
    (id : Nat) (uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing)
    (root : Goose.Core.RootInst)
    (resolved : rootOf (frame.interpretation.enterScope scope state.nextScope).environment id
      { state with nextScope := state.nextScope + 1 } = .ok root { state with nextScope := state.nextScope + 1 }) :
    types root = none := by
  have actual := rootOf_instantiates (frame.interpretation.enterScope scope state.nextScope) id _ root resolved
  cases actual with
  | «local» id descriptor scopeInst declared active =>
    change frame.interpretation.environment.vars[id]? = some descriptor at declared
    by_cases same : descriptor.scope = scope
    · have resolvedCurrent := rootOf_enterScope_current frame.interpretation scope state.nextScope id descriptor
        { state with nextScope := state.nextScope + 1 } declared same
      have equal := (ExecutionStep.ok.inj (resolved.symm.trans resolvedCurrent)).1
      rw [equal]
      exact world.freshScope_localType frame.interpretation.environment.act id
    · have different : (scope == descriptor.scope) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simp only [RootInterpretation.enterScope, List.find?_cons, different] at active
      have prior : rootOf frame.interpretation.environment id state =
          .ok (.local frame.interpretation.environment.act scopeInst id) state := by
        simp only [rootOf, declared, active, pure]
      exact source.uninitializedTypes id uninitialized _ prior

theorem AcceptedFrame.registerLocal_preserves_other_uninitializedTypes
    {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id other : Nat) (root otherRoot : Goose.Core.RootInst)
    (ty : Ty) (different : other ≠ id)
    (uninitialized : frame.rootCursor.nextVar ≤ other ∨ other ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state)
    (otherResolved : rootOf frame.interpretation.environment other state = .ok otherRoot state) :
    registerRootType types root ty otherRoot = none := by
  have rootsDifferent : otherRoot ≠ root := by
    intro equal
    subst otherRoot
    exact different (rootOf_variable_injective frame.interpretation other id state root otherResolved resolved)
  simp only [registerRootType, rootsDifferent, ↓reduceIte]
  exact source.uninitializedTypes other uninitialized otherRoot otherResolved

theorem AcceptedFrame.enterInitializer_order {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (ordered : id = frame.rootCursor.nextVar) :
    ∀ other ∈ id :: frame.source.initializing, other < frame.rootCursor.nextVar + 1 := by
  intro other member
  rcases List.mem_cons.mp member with same | existing
  · rw [same, ordered]
    exact Nat.lt_succ_self _
  · exact Nat.lt_trans (source.initializingBefore other existing) (Nat.lt_succ_self _)

theorem AcceptedFrame.registerLocal_advance_uninitializedTypes
    {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id other : Nat) (root otherRoot : Goose.Core.RootInst)
    (ty : Ty) (ordered : id = frame.rootCursor.nextVar)
    (uninitialized : frame.rootCursor.nextVar + 1 ≤ other ∨ other ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state)
    (otherResolved : rootOf frame.interpretation.environment other state = .ok otherRoot state) :
    registerRootType types root ty otherRoot = none := by
  have different : other ≠ id := by
    intro equal
    subst other
    rcases uninitialized with future | initializing
    · omega
    · have prior := source.initializingBefore id initializing
      rw [ordered] at prior
      exact (Nat.lt_irrefl _ prior).elim
  have prior : frame.rootCursor.nextVar ≤ other ∨ other ∈ frame.source.initializing := by
    rcases uninitialized with future | initializing
    · exact Or.inl (Nat.le_trans (Nat.le_succ _) future)
    · exact Or.inr initializing
  exact source.registerLocal_preserves_other_uninitializedTypes id other root otherRoot ty different prior resolved otherResolved

#print axioms AcceptedWorld.freshScope_localType
#print axioms AcceptedWorld.enterScope_localType
#print axioms AcceptedFrame.enterScope_uninitializedTypes
#print axioms AcceptedFrame.registerLocal_preserves_other_uninitializedTypes
#print axioms AcceptedFrame.enterInitializer_order
#print axioms AcceptedFrame.registerLocal_advance_uninitializedTypes

end Goose.Proofs.ConstructionAcceptedExecution
