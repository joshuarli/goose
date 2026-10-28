import Goose.Proofs.ConstructionAcceptedMixedLocalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindRoot_existingScalar_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (root : RootInst) (ty : Ty) (value : Value)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (ordinal : Nat) (existing : before.objectOrdinals.lookup root = some ordinal)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root value before = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other) regions pending := by
  let reserved := before
  let after := { before with objects := (root, value) :: before.objects.filter (fun entry => entry.1 != root) }
  have actual : bindRoot root value before = .ok () after := by
    simp [bindRoot, existing, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
  have base := world
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


theorem bindRoot_scalar_update_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (root : RootInst) (ty : Ty) (value : Value)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (rootType : types root = some ty) (retained : live root)
    (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value) :
    ∃ after, bindRoot root value before = .ok () after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  have compatible : RootTypeCompatible types root ty := by
    intro previous present
    exact Option.some.inj (present.symm.trans rootType)
  have conform := world.layouts root ty rootType
  have freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope := by
    intro act scope id equal
    exact world.typeFrontier act scope id ty (by simpa [equal] using rootType)
  have freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope := by
    intro id equal outside
    exact world.syntheticFrontier id ty (by simpa [equal] using rootType) outside
  have sameTypes : registerRootType types root ty = types := by
    funext other
    by_cases same : other = root
    · subst other; simp [registerRootType, rootType]
    · simp [registerRootType, same]
  have sameLive : (fun other => other = root ∨ live other) = live := by
    funext other
    apply propext
    constructor
    · intro member; rcases member with same | old
      · subst other; exact retained
      · exact old
    · intro old; exact Or.inr old
  cases existing : before.objectOrdinals.lookup root with
  | none =>
    obtain ⟨after, bound, extended, afterWorld⟩ := bindRoot_freshScalar_world config initialized before ambient types live root ty value
      regions pending world scalar existing compatible conform represented pointers freshType freshSynthetic
    rw [sameTypes, sameLive] at afterWorld
    exact ⟨after, bound, afterWorld⟩
  | some ordinal =>
    obtain ⟨after, bound, extended, afterWorld⟩ := bindRoot_existingScalar_world config initialized before ambient types live root ty value
      regions pending world scalar ordinal existing compatible conform represented pointers freshType freshSynthetic
    rw [sameTypes, sameLive] at afterWorld
    exact ⟨after, bound, afterWorld⟩

#print axioms bindRoot_scalar_update_world
#print axioms bindRoot_existingScalar_world
end Goose.Proofs.ConstructionAcceptedExecution
