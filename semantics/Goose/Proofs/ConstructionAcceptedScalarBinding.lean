import Goose.Proofs.ConstructionAcceptedScalarLocal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindRoot_freshScalar_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (root : RootInst) (ty : Ty) (value : Value)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (fresh : before.objectOrdinals.lookup root = none)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root value before = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other) regions pending := by
  let reserved := reserveByteStorage before
  let after := { reserved with
    objects := (root, value) :: before.objects.filter (fun entry => entry.1 != root)
    objectOrdinals := (root, before.construction.storage.size) :: before.objectOrdinals.filter (fun entry => entry.1 != root) }
  have actual : bindRoot root value before = .ok () after := bindRoot_freshScalar before root value scalar fresh
  have base := reserveByteStorage_world config initialized before ambient types live regions pending world
  obtain ⟨heapState, heapBound, extended, heap⟩ := bindRoot_registeredHeap types before root ty value compatible world.heap represented pointers
  have same := (ExecutionStep.ok.inj (heapBound.symm.trans actual)).2
  subst heapState
  have construction : after.construction = reserved.construction := rfl
  have notStored : ∀ stored, value ≠ .stored stored := by
    intro stored equal
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases equal
  have valueBacking : ValueStorageBacked config.layout after value := by
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩
    · exact .integer intTy number
    · exact .boolean boolean
  have context : OwnershipExecutionContext after ambient := by
    exact ⟨base.ownership.source, base.ownership.retention,
      ⟨base.ownership.runtime.activations, base.ownership.runtime.breaks⟩, base.ownership.reservations,
      base.ownership.receiving, base.ownership.bounds,
      ⟨base.ownership.identities.activations, base.ownership.identities.breaks⟩⟩
  have backing : RootedBackingState config.layout after (fun other => other = root ∨ live other) := by
    constructor
    · intro other retained item present
      by_cases same : other = root
      · subst other
        have equal : value = item := by simpa [after] using present
        subst item; exact valueBacking
      · have old : before.objects.lookup other = some item := by
          rw [← bindRoot_lookup_other root other value before after actual same]; exact present
        exact ValueStorageBacked.construction_frame construction (base.backing.values other (retained.resolve_left same) item old)
    · intro other retained stored present
      by_cases same : other = root
      · subst other
        have equal : value = .stored stored := by simpa [after] using present
        exact (notStored stored equal).elim
      · have old : before.objects.lookup other = some (.stored stored) := by
          rw [← bindRoot_lookup_other root other value before after actual same]; exact present
        rw [bindRoot_ordinals_other root other value before after actual same]
        exact base.backing.identities other (retained.resolve_left same) stored old
  refine ⟨after, actual, extended, ⟨context, ?_, ?_, ?_, ?_, ?_, heap, ?_, ?_, backing, ?_, ?_⟩, ?_⟩
  · refine ⟨world.globals.1, ?_⟩
    intro id available
    obtain ⟨descriptor, old, declared, found, oldRepresented⟩ := world.globals.2 id available
    by_cases same : RootInst.global id = root
    · have present : after.objects.lookup (.global id) = some value := by simp [after, same]
      exact ⟨descriptor, value, declared, present,
        (heap _ _ _ (extended _ _ (world.globalTypes id descriptor declared)) present).1⟩
    · have present : after.objects.lookup (.global id) = some old := by
        rw [bindRoot_lookup_other root (.global id) value before after actual same]; exact found
      exact ⟨descriptor, old, declared, present, oldRepresented⟩
  · intro id descriptor declared; exact extended _ _ (world.globalTypes id descriptor declared)
  · exact registerRootType_layouts config.layout types root ty world.layouts conforms
  · exact registerRootType_frontier types before root ty world.typeFrontier freshType
  · exact registerRootType_synthetic_frontier config types before root ty world.syntheticFrontier freshSynthetic
  · intro other item present
    by_cases same : other = root
    · subst other; exact ⟨ty, by simp [registerRootType]⟩
    · rw [bindRoot_lookup_other root other value before after actual same] at present
      obtain ⟨oldTy, declared⟩ := world.objectsRegistered other item present
      exact ⟨oldTy, extended other oldTy declared⟩
  · intro other ordinal present
    by_cases same : other = root
    · subst other; exact ⟨ty, by simp [registerRootType]⟩
    · rw [bindRoot_ordinals_other root other value before after actual same] at present
      obtain ⟨oldTy, declared⟩ := world.ordinalsRegistered other ordinal present
      exact ⟨oldTy, extended other oldTy declared⟩
  · intro region member
    have valid := base.protections region member
    refine ⟨by simpa only [construction] using valid.present, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, valid.authority,
      by simpa only [construction] using valid.authorityBound, ?_⟩
    · intro other retained item found; exact backing.values other retained.1 item found
    · intro other retained item found; exact backing.identities other retained.1 item found
    · intro other retained item found stored occurrence
      by_cases same : other = root
      · subst other
        have equal : value = item := by simpa [after] using found
        subst item
        rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases occurrence
      · have old : before.objects.lookup other = some item := by
          rw [← bindRoot_lookup_other root other value before after actual same]; exact found
        exact (valid.observations.observations other ⟨retained.1.resolve_left same, retained.2⟩ item old stored occurrence).construction_frame
          config.layout reserved after region.limit stored construction
    · intro row found; exact valid.cutoff row (by simpa only [construction] using found)
    · intro row found; exact valid.landing row (by simpa only [construction] using found)
    · intro other retained outside item found stored occurrence id named
      by_cases same : other = root
      · subst other
        have equal : value = item := by simpa [after] using found
        subst item
        rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases occurrence
      · have old : before.objects.lookup other = some item := by
          rw [← bindRoot_lookup_other root other value before after actual same]; exact found
        exact valid.names other (retained.resolve_left same) outside item old stored occurrence id named
  · intro carrierFrame member
    obtain ⟨ready, backed⟩ := base.carriers carrierFrame member
    exact ⟨⟨ready.lengths, fun channel carrier pair =>
      carrierReady_construction_frame reserved after construction channel carrier (ready.pairs channel carrier pair)⟩,
      fun carrier present => carrierBacking_construction_frame config.layout reserved after construction carrier (backed carrier present)⟩
  · intro id available; exact Or.inr (world.globalLive id available)

theorem AcceptedFrame.bindFreshScalar_correspondence
    {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (id : Nat) (root : RootInst) (value : Value)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing)
    (resolved : rootOf frame.interpretation.environment id before = .ok root before)
    (bound : bindRoot root value before = .ok () after) :
    LocalRootCorrespondence frame.interpretation frame.source.ctx (id :: frame.typing.visible) after ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx
        (id :: frame.typing.visible) fuel config.layout after := by
  have rooted : LocalValueRooted frame.interpretation frame.source.ctx id value := by
    intro location reference
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases reference
  obtain ⟨directAfter, directBound, direct⟩ := bindRoot_localValueCorrespondence frame.interpretation frame.source.ctx
    frame.typing.visible before id root value resolved rooted source.direct
  have directSame := (ExecutionStep.ok.inj (bound.symm.trans directBound)).2
  subst directAfter
  refine ⟨direct, ?_⟩
  intro fuel
  have contentsRooted : LocalValueContentsRooted frame.interpretation frame.source.ctx id value fuel config.layout before := by
    intro roots annotation location equal
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases equal
  have separateValue : ∀ location, value = .ref location → location.root ≠ root := by
    intro location equal
    rcases scalar with ⟨intTy, number, rfl⟩ | ⟨boolean, rfl⟩ <;> cases equal
  have separateVisible : ∀ other ∈ frame.typing.visible, ∀ actual location,
      rootOf frame.interpretation.environment other before = .ok actual before →
      before.objects.lookup actual = some (.ref location) → location.root ≠ root := by
    intro other member actual location otherResolved found
    exact source.visibleReferences_avoid_uninitialized world id root uninitialized resolved other member actual location otherResolved found
  obtain ⟨contentAfter, contentBound, contents⟩ := bindRoot_localContentsCorrespondence frame.interpretation frame.source.ctx
    frame.typing.visible before fuel config.layout id root value resolved contentsRooted separateValue separateVisible
    (source.contents fuel)
  have contentSame := (ExecutionStep.ok.inj (bound.symm.trans contentBound)).2
  subst contentAfter
  exact contents

theorem AcceptedFrame.bindFreshScalar_advance {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (id : Nat) (descriptor : LocalVar) (root : Goose.Core.RootInst) (value : Value)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor) (represented : ValueRepresentation descriptor.ty value)
    (resolved : rootOf frame.interpretation.environment id before = .ok root before)
    (bound : bindRoot root value before = .ok () after) :
    AcceptedFrame config accepted (advanceLocalFrame frame id) after (registerRootType types root descriptor.ty) := by
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing :=
    Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  have fresh := (source.uninitializedLocals id uninitialized root resolved).2
  have same := (ExecutionStep.ok.inj (bound.symm.trans (bindRoot_freshScalar before root value scalar fresh))).2
  have controls : after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope := by
    rw [same]
    exact ⟨rfl, rfl⟩
  obtain ⟨objectState, objectBound, objects⟩ := bindRoot_objects root value before
  have objectSame := (ExecutionStep.ok.inj (bound.symm.trans objectBound)).2
  subst objectState
  have currentObject : after.objects.lookup root = some value := by
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
  obtain ⟨direct, contents⟩ := source.bindFreshScalar_correspondence world id root value scalar uninitialized resolved bound
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
      exact ⟨descriptor, root, value, runtimeDeclared,
        rootOf_transfer frame.interpretation id before after root resolved, currentObject,
        represented⟩
    · obtain ⟨oldDescriptor, oldRoot, oldValue, oldDeclared, oldResolved, found, represented⟩ := source.locals other old
      have different := oldRootDifferent other old oldRoot oldResolved
      exact ⟨oldDescriptor, oldRoot, oldValue, oldDeclared,
        rootOf_transfer frame.interpretation other before after oldRoot oldResolved,
        (bindRoot_lookup_other root oldRoot value before after bound different).trans found, represented⟩
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
    exact ⟨(bindRoot_lookup_other root otherRoot value before after bound rootsDifferent).trans absent,
      (bindRoot_ordinals_other root otherRoot value before after bound rootsDifferent).trans ordinal⟩
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
    exact ⟨(bindRoot_lookup_other root (.global global) value before after bound different).trans absent,
      (bindRoot_ordinals_other root (.global global) value before after bound different).trans ordinal⟩


#print axioms AcceptedFrame.bindFreshScalar_advance
#print axioms bindRoot_freshScalar_world
end Goose.Proofs.ConstructionAcceptedExecution
