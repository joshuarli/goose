import Goose.Proofs.ConstructionAcceptedLocalSeparation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def advanceLocalFrame (frame : ConstructionSourceFrame) (id : Nat) : ConstructionSourceFrame :=
  { frame with
    typing := { frame.typing with visible := id :: frame.typing.visible }
    typingCounter := frame.typingCounter + 1
    rootCursor := { frame.rootCursor with nextVar := frame.rootCursor.nextVar + 1 } }

theorem AcceptedFrame.advanceLocal_compatible {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id : Nat) (descriptor : LocalVar)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor) :
    SourceFrameCompatible accepted (advanceLocalFrame frame id) := by
  have bound := (Array.getElem?_eq_some_iff.mp declared).1
  refine ⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
    source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
    source.compatible.globals, source.compatible.initialized, ?_, ?_, ?_, ?_, source.compatible.currentScope,
    source.compatible.origin⟩
  · change frame.rootCursor.nextVar + 1 ≤ frame.typingCounter + 1
    exact Nat.succ_le_succ source.compatible.declarations
  · change frame.typingCounter + 1 ≤ frame.typing.variables.size
    rw [← typingOrder]
    omega
  · intro other member
    change other ∈ id :: frame.typing.visible at member
    change other < frame.rootCursor.nextVar + 1
    rcases List.mem_cons.mp member with same | old
    · rw [same, rootOrder]
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (source.compatible.visible other old) (Nat.lt_succ_self _)
  · intro other initializing visible
    change other ∈ id :: frame.typing.visible at visible
    rcases List.mem_cons.mp visible with same | old
    · have earlier := source.initializingBefore other initializing
      rw [same, rootOrder] at earlier
      exact (Nat.lt_irrefl _ earlier).elim
    · exact source.compatible.initializing other initializing old

theorem AcceptedFrame.bindFreshStored_advance {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (id : Nat) (descriptor : LocalVar) (root : Goose.Core.RootInst) (stored : StoredValue)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor) (valueType : stored.ty = descriptor.ty)
    (nonfixed : descriptor.ty.nonfixed = true)
    (resolved : rootOf frame.interpretation.environment id before = .ok root before)
    (bound : bindRoot root (.stored stored) before = .ok () after) :
    AcceptedFrame config accepted (advanceLocalFrame frame id) after (registerRootType types root descriptor.ty) := by
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing :=
    Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  have controls : after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope := by
    cases ordinal : before.objectOrdinals.lookup root <;>
      simp only [bindRoot, bind, EvalM.get, ordinal, Option.isNone, Bool.false_eq_true, ite_false,
        ite_true, setObjectOrdinal, bindStaticRoot, EvalM.set] at bound <;>
      cases bound <;> exact ⟨rfl, rfl⟩
  obtain ⟨objectState, objectBound, objects⟩ := bindRoot_objects root (.stored stored) before
  have objectSame := (ExecutionStep.ok.inj (bound.symm.trans objectBound)).2
  subst objectState
  have currentObject : after.objects.lookup root = some (.stored stored) := by
    rw [objects]
    simp only [List.lookup, beq_self_eq_true]
  have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]
    exact declared
  have extended : RootTypesExtend types (registerRootType types root descriptor.ty) := by
    apply registerRootType_extends
    intro previous present
    rw [source.uninitializedTypes id uninitialized root resolved] at present
    cases present
  have oldRootDifferent : ∀ other ∈ frame.typing.visible, ∀ otherRoot,
      rootOf frame.interpretation.environment other before = .ok otherRoot before → otherRoot ≠ root := by
    intro other member otherRoot otherResolved same
    subst otherRoot
    have idSame := rootOf_variable_injective frame.interpretation other id before root otherResolved resolved
    have earlier := source.compatible.visible other member
    rw [idSame, rootOrder] at earlier
    exact Nat.lt_irrefl _ earlier
  obtain ⟨direct, contents⟩ := source.bindFreshStored_correspondence world id root stored uninitialized resolved bound
  refine ⟨source.advanceLocal_compatible id descriptor rootOrder typingOrder declared, ?_, ?_, ?_, source.aliases,
    ?_, ?_, ?_, ?_, ?_, direct, contents⟩
  · simpa only [advanceLocalFrame, controls.1] using source.frontier
  · simpa only [advanceLocalFrame, controls.2] using source.scopeFrontier
  · intro other member
    change other < frame.rootCursor.nextVar + 1
    exact Nat.lt_trans (source.initializingBefore other member) (Nat.lt_succ_self _)
  · intro other member
    change other ∈ id :: frame.typing.visible at member
    rcases List.mem_cons.mp member with same | old
    · subst other
      exact ⟨descriptor, root, .stored stored, runtimeDeclared,
        rootOf_transfer frame.interpretation id before after root resolved, currentObject,
        .stored descriptor.ty stored nonfixed valueType⟩
    · obtain ⟨oldDescriptor, oldRoot, value, oldDeclared, oldResolved, found, represented⟩ := source.locals other old
      have different := oldRootDifferent other old oldRoot oldResolved
      exact ⟨oldDescriptor, oldRoot, value, oldDeclared,
        rootOf_transfer frame.interpretation other before after oldRoot oldResolved,
        (bindRoot_lookup_other root oldRoot (.stored stored) before after bound different).trans found, represented⟩
  · intro other member oldDescriptor otherRoot oldDeclared otherResolved
    change other ∈ id :: frame.typing.visible at member
    have prior := rootOf_transfer frame.interpretation other after before otherRoot otherResolved
    rcases List.mem_cons.mp member with same | old
    · subst other
      have rootSame := (ExecutionStep.ok.inj (prior.symm.trans resolved)).1
      subst otherRoot
      have descriptorSame := Option.some.inj (oldDeclared.symm.trans declared)
      subst oldDescriptor
      simp only [registerRootType, ↓reduceIte]
    · have previous := source.localTypes other old oldDescriptor otherRoot oldDeclared prior
      exact extended otherRoot oldDescriptor.ty previous
  · intro other condition otherRoot otherResolved
    change frame.rootCursor.nextVar + 1 ≤ other ∨ other ∈ frame.source.initializing at condition
    have prior := rootOf_transfer frame.interpretation other after before otherRoot otherResolved
    have different : other ≠ id := by
      intro equal
      subst other
      rcases condition with future | initializing
      · rw [rootOrder] at future
        omega
      · have earlier := source.initializingBefore id initializing
        rw [rootOrder] at earlier
        exact Nat.lt_irrefl _ earlier
    have oldCondition : frame.rootCursor.nextVar ≤ other ∨ other ∈ frame.source.initializing := by
      rcases condition with future | initializing
      · exact Or.inl (Nat.le_trans (Nat.le_succ _) future)
      · exact Or.inr initializing
    have rootsDifferent : otherRoot ≠ root := by
      intro same
      subst otherRoot
      exact different (rootOf_variable_injective frame.interpretation other id before root prior resolved)
    obtain ⟨absent, ordinal⟩ := source.uninitializedLocals other oldCondition otherRoot prior
    exact ⟨(bindRoot_lookup_other root otherRoot (.stored stored) before after bound rootsDifferent).trans absent,
      (bindRoot_ordinals_other root otherRoot (.stored stored) before after bound rootsDifferent).trans ordinal⟩
  · intro other condition otherRoot otherResolved
    change frame.rootCursor.nextVar + 1 ≤ other ∨ other ∈ frame.source.initializing at condition
    have prior := rootOf_transfer frame.interpretation other after before otherRoot otherResolved
    exact source.registerLocal_advance_uninitializedTypes id other root otherRoot descriptor.ty rootOrder condition resolved prior
  · intro global future inside
    have different : Goose.Core.RootInst.global global ≠ root := by
      obtain ⟨scope, same⟩ := rootOf_variable frame.interpretation id before root resolved
      rw [same]
      intro impossible
      cases impossible
    obtain ⟨absent, ordinal⟩ := source.futureGlobals global future inside
    exact ⟨(bindRoot_lookup_other root (.global global) (.stored stored) before after bound different).trans absent,
      (bindRoot_ordinals_other root (.global global) (.stored stored) before after bound different).trans ordinal⟩

#print axioms AcceptedFrame.advanceLocal_compatible
#print axioms AcceptedFrame.bindFreshStored_advance

end Goose.Proofs.ConstructionAcceptedExecution
