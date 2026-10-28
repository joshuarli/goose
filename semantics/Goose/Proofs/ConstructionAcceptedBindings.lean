import Goose.Proofs.ConstructionAcceptedFreshness
import Goose.Proofs.ConstructionRootCorrespondenceWrites
import Goose.Proofs.ConstructionReadTypingLayout

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def RootTypesExtend (before after : RootTypes) : Prop :=
  ∀ root ty, before root = some ty → after root = some ty

def registerRootType (types : RootTypes) (root : RootInst) (ty : Ty) : RootTypes :=
  fun other => if other = root then some ty else types other

def RootTypeCompatible (types : RootTypes) (root : RootInst) (ty : Ty) : Prop :=
  ∀ previous, types root = some previous → previous = ty

theorem registerRootType_extends (types : RootTypes) (root : RootInst) (ty : Ty)
    (compatible : RootTypeCompatible types root ty) : RootTypesExtend types (registerRootType types root ty) := by
  intro other previous present
  by_cases same : other = root
  · subst other
    rw [compatible previous present]
    simp only [registerRootType, ↓reduceIte]
  · simp only [registerRootType, same, ↓reduceIte]
    exact present

theorem LocationTyped.types_extend (before after : RootTypes) (extended : RootTypesExtend before after)
    (location : Goose.Core.Loc) (ty : Ty) (valid : LocationTyped before location ty) :
    LocationTyped after location ty := by
  obtain ⟨rootType, declared, path⟩ := valid
  exact ⟨rootType, extended location.root rootType declared, path⟩

theorem PointerTypedValue.types_extend (before after : RootTypes) (extended : RootTypesExtend before after)
    (ty : Ty) (value : Value) (valid : PointerTypedValue before ty value) : PointerTypedValue after ty value := by
  induction valid with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference mutability ty location target =>
    exact .reference mutability ty location (target.types_extend before after extended location ty)
  | slice mutability ty owner location start count target sequence =>
    exact .slice mutability ty owner location start count
      (target.types_extend before after extended location owner) sequence
  | array element count values children ih => exact .array element count values ih
  | record id fields values children ih => exact .record id fields values ih
  | stored ty value => exact .stored ty value

theorem registerRootType_frontier (types : RootTypes) (state : ExecutionState)
    (root : RootInst) (ty : Ty)
    (previous : ∀ act scope id ty, types (.local act scope id) = some ty →
      act < state.nextAct ∧ scope < state.nextScope)
    (fresh : ∀ act scope id, root = .local act scope id → act < state.nextAct ∧ scope < state.nextScope) :
    ∀ act scope id otherTy, registerRootType types root ty (.local act scope id) = some otherTy →
      act < state.nextAct ∧ scope < state.nextScope := by
  intro act scope id registered present
  by_cases same : RootInst.local act scope id = root
  · exact fresh act scope id same.symm
  · exact previous act scope id registered (by simpa only [registerRootType, same, ↓reduceIte] using present)

theorem registerRootType_layouts (layout : LayoutEnv) (types : RootTypes) (root : RootInst) (ty : Ty)
    (previous : ∀ other previousTy, types other = some previousTy → LayoutConforms layout previousTy)
    (conforms : LayoutConforms layout ty) :
    ∀ other registeredTy, registerRootType types root ty other = some registeredTy → LayoutConforms layout registeredTy := by
  intro other registeredTy present
  by_cases same : other = root
  · subst other
    have typeSame : ty = registeredTy := by simpa only [registerRootType, ↓reduceIte, Option.some.injEq] using present
    simpa only [← typeSame] using conforms
  · exact previous other registeredTy (by simpa only [registerRootType, same, ↓reduceIte] using present)

theorem registerRootType_synthetic_frontier (config : EvalConfig) (types : RootTypes) (state : ExecutionState)
    (root : RootInst) (ty : Ty)
    (previous : ∀ id previousTy, types (.global id) = some previousTy → config.module.globals.size ≤ id →
      id < config.module.globals.size + state.nextScope)
    (fresh : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + state.nextScope) :
    ∀ id registeredTy, registerRootType types root ty (.global id) = some registeredTy →
      config.module.globals.size ≤ id → id < config.module.globals.size + state.nextScope := by
  intro id registeredTy present outside
  by_cases same : RootInst.global id = root
  · exact fresh id same.symm outside
  · exact previous id registeredTy (by simpa only [registerRootType, same, ↓reduceIte] using present) outside

theorem bindRoot_registeredHeap (types : RootTypes) (before : ExecutionState) (root : RootInst)
    (ty : Ty) (value : Value) (compatible : RootTypeCompatible types root ty)
    (previous : ∀ other otherTy item, types other = some otherTy → before.objects.lookup other = some item →
      ValueRepresentation otherTy item ∧ PointerTypedValue types otherTy item)
    (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value) :
    ∃ after, bindRoot root value before = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      ∀ other otherTy item, registerRootType types root ty other = some otherTy →
        after.objects.lookup other = some item → ValueRepresentation otherTy item ∧
          PointerTypedValue (registerRootType types root ty) otherTy item := by
  obtain ⟨after, bound, objects⟩ := bindRoot_objects root value before
  have extended := registerRootType_extends types root ty compatible
  refine ⟨after, bound, extended, ?_⟩
  intro other otherTy item declared present
  by_cases same : other = root
  · subst other
    have typeSame : ty = otherTy := by simpa only [registerRootType, ↓reduceIte, Option.some.injEq] using declared
    have valueSame : value = item := by simpa only [objects, List.lookup, beq_self_eq_true, Option.some.injEq] using present
    subst otherTy item
    exact ⟨represented, pointers.types_extend types _ extended ty value⟩
  · have oldDeclared : types other = some otherTy := by simpa only [registerRootType, same, ↓reduceIte] using declared
    have oldPresent := (bindRoot_lookup_other root other value before after bound same).symm.trans present
    have valid := previous other otherTy item oldDeclared oldPresent
    exact ⟨valid.1, valid.2.types_extend types _ extended otherTy item⟩

theorem bindRoot_stored_context (before : ExecutionState) (ambient : OwnershipAmbient)
    (root : RootInst) (stored : StoredValue) (valid : OwnershipExecutionContext before ambient) :
    ∃ after, bindRoot root (.stored stored) before = .ok () after ∧ OwnershipExecutionContext after ambient := by
  cases ordinal : before.objectOrdinals.lookup root with
  | none =>
    let after := { before with
      objects := (root, .stored stored) :: before.objects.filter (fun entry => entry.1 != root)
      objectOrdinals := (root, stored.object.getD stored.storage) :: before.objectOrdinals.filter (fun entry => entry.1 != root) }
    refine ⟨after, ?_, ?_⟩
    · simp [bindRoot, ordinal, setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
    · exact ⟨valid.source, valid.retention, ⟨valid.runtime.activations, valid.runtime.breaks⟩,
        valid.reservations, valid.receiving, valid.bounds, ⟨valid.identities.activations, valid.identities.breaks⟩⟩
  | some ordinal =>
    let after := { before with
      objects := (root, .stored stored) :: before.objects.filter (fun entry => entry.1 != root) }
    refine ⟨after, ?_, ?_⟩
    · simp [bindRoot, ordinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
    · exact ⟨valid.source, valid.retention, ⟨valid.runtime.activations, valid.runtime.breaks⟩,
        valid.reservations, valid.receiving, valid.bounds, ⟨valid.identities.activations, valid.identities.breaks⟩⟩

theorem bindRoot_freshStored_registered (layout : LayoutEnv) (types : RootTypes)
    (before : ExecutionState) (ambient : OwnershipAmbient) (liveRoots : RootInst → Prop)
    (root : RootInst) (ty : Ty) (stored : StoredValue)
    (context : OwnershipExecutionContext before ambient) (backing : RootedBackingState layout before liveRoots)
    (heap : ∀ other otherTy item, types other = some otherTy → before.objects.lookup other = some item →
      ValueRepresentation otherTy item ∧ PointerTypedValue types otherTy item)
    (compatible : RootTypeCompatible types root ty) (represented : ValueRepresentation ty (.stored stored))
    (backed : StoredValueBacking layout before stored) (fresh : before.objectOrdinals.lookup root = none) :
    ∃ after, bindRoot root (.stored stored) before = .ok () after ∧
      OwnershipExecutionContext after ambient ∧
      RootedBackingState layout after (fun other => other = root ∨ liveRoots other) ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      (∀ other otherTy item, registerRootType types root ty other = some otherTy →
        after.objects.lookup other = some item → ValueRepresentation otherTy item ∧
          PointerTypedValue (registerRootType types root ty) otherTy item) ∧
      after.construction = before.construction := by
  obtain ⟨after, evaluated, context⟩ := bindRoot_stored_context before ambient root stored context
  obtain ⟨backedAfter, backedResult, validBacking, construction⟩ :=
    bindRoot_freshStored_backing layout before liveRoots root stored backing backed fresh
  have same := evaluated.symm.trans backedResult
  cases same
  obtain ⟨typedAfter, typedResult, extended, validHeap⟩ := bindRoot_registeredHeap types before root ty
    (.stored stored) compatible heap represented (.stored ty stored)
  have same := evaluated.symm.trans typedResult
  cases same
  exact ⟨after, evaluated, context, validBacking, extended, validHeap, construction⟩

theorem bindRoot_freshStored_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : RootInst → Prop) (root : RootInst) (ty : Ty) (stored : StoredValue)
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized before ambient types liveRoots regions pending)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (represented : ValueRepresentation ty (.stored stored)) (backed : StoredValueBacking config.layout before stored)
    (fresh : before.objectOrdinals.lookup root = none)
    (regionSafety : ∀ region ∈ regions, ¬ region.mutableRoots root →
      StoredBackingObservation config.layout before region.limit stored ∧
        ∀ id, stored.destination = some id → id ∉ region.mutableDestinations)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root (.stored stored) before = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ liveRoots other) regions pending := by
  let after := { before with
    objects := (root, .stored stored) :: before.objects.filter (fun entry => entry.1 != root)
    objectOrdinals := (root, stored.object.getD stored.storage) :: before.objectOrdinals.filter (fun entry => entry.1 != root) }
  have actual : bindRoot root (.stored stored) before = .ok () after := by
    simp [bindRoot, fresh, setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
  obtain ⟨middle, evaluated, context, backing, extended, heap, construction⟩ :=
    bindRoot_freshStored_registered config.layout types before ambient liveRoots root ty stored world.ownership
      world.backing world.heap compatible represented backed fresh
  have same := (ExecutionStep.ok.inj (evaluated.symm.trans actual)).2
  subst middle
  refine ⟨after, actual, extended, ⟨context, ?_, ?_, ?_, ?_, ?_, heap, ?_, ?_, backing, ?_, ?_⟩, ?_⟩
  · refine ⟨world.globals.1, ?_⟩
    intro id available
    obtain ⟨descriptor, old, declared, found, represented⟩ := world.globals.2 id available
    by_cases same : RootInst.global id = root
    · have present : after.objects.lookup (.global id) = some (.stored stored) := by
        simp only [after, same, List.lookup, beq_self_eq_true]
      exact ⟨descriptor, .stored stored, declared, present,
        (heap _ _ _ (extended _ _ (world.globalTypes id descriptor declared)) present).1⟩
    · have present : after.objects.lookup (.global id) = some old := by
        rw [bindRoot_lookup_other root (.global id) (.stored stored) before after actual same]
        exact found
      exact ⟨descriptor, old, declared, present, represented⟩
  · intro id descriptor declared
    exact extended _ _ (world.globalTypes id descriptor declared)
  · exact registerRootType_layouts config.layout types root ty world.layouts conforms
  · exact registerRootType_frontier types before root ty world.typeFrontier freshType
  · exact registerRootType_synthetic_frontier config types before root ty world.syntheticFrontier freshSynthetic
  · intro other value present
    by_cases same : other = root
    · subst other
      exact ⟨ty, by simp only [registerRootType, ↓reduceIte]⟩
    · rw [bindRoot_lookup_other root other (.stored stored) before after actual same] at present
      obtain ⟨oldTy, declared⟩ := world.objectsRegistered other value present
      exact ⟨oldTy, extended other oldTy declared⟩
  · intro other ordinal present
    by_cases same : other = root
    · subst other
      exact ⟨ty, by simp only [registerRootType, ↓reduceIte]⟩
    · rw [bindRoot_ordinals_other root other (.stored stored) before after actual same] at present
      obtain ⟨oldTy, declared⟩ := world.ordinalsRegistered other ordinal present
      exact ⟨oldTy, extended other oldTy declared⟩
  · intro region member
    have valid := world.protections region member
    refine ⟨by simpa only [construction] using valid.present, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, valid.authority, ?_⟩
    · intro other retained value found
      exact backing.values other retained.1 value found
    · intro other retained value found
      exact backing.identities other retained.1 value found
    · intro other retained value found item occurrence
      by_cases same : other = root
      · subst other
        have equal : Value.stored stored = value := by
          simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using found
        subst value
        cases occurrence
        exact ((regionSafety region member retained.2).1).construction_frame
          config.layout before after region.limit stored construction
      · have old : before.objects.lookup other = some value := by
          rw [← bindRoot_lookup_other root other (.stored stored) before after actual same]
          exact found
        exact (valid.observations.observations other ⟨retained.1.resolve_left same, retained.2⟩ value old item occurrence).construction_frame
          config.layout before after region.limit item construction
    · intro row found
      exact valid.cutoff row (by simpa only [construction] using found)
    · intro row found
      exact valid.landing row (by simpa only [construction] using found)
    · intro other retained outside value found item occurrence id named
      by_cases same : other = root
      · subst other
        have equal : Value.stored stored = value := by
          simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using found
        subst value
        cases occurrence
        exact (regionSafety region member outside).2 id named
      · have old : before.objects.lookup other = some value := by
          rw [← bindRoot_lookup_other root other (.stored stored) before after actual same]
          exact found
        exact valid.names other (retained.resolve_left same) outside value old item occurrence id named
  · intro frame member
    obtain ⟨ready, backed⟩ := world.carriers frame member
    exact ⟨⟨ready.lengths, fun channel carrier pair =>
      carrierReady_construction_frame before after construction channel carrier (ready.pairs channel carrier pair)⟩,
      fun carrier present => carrierBacking_construction_frame config.layout before after construction carrier (backed carrier present)⟩
  · intro id available
    exact Or.inr (world.globalLive id available)

theorem bindRoot_freshGlobalStored_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (descriptor : Global) (stored : StoredValue)
    (world : AcceptedWorld config initialized before ambient types liveRoots [] [])
    (declared : config.module.globals[initialized]? = some descriptor)
    (represented : ValueRepresentation descriptor.ty (.stored stored))
    (backed : StoredValueBacking config.layout before stored)
    (fresh : before.objectOrdinals.lookup (.global initialized) = none) :
    ∃ after, bindRoot (.global initialized) (.stored stored) before = .ok () after ∧
      AcceptedWorld config (initialized + 1) after ambient types
        (fun root => root = .global initialized ∨ liveRoots root) [] [] := by
  have registered := world.globalTypes initialized descriptor declared
  have compatible : RootTypeCompatible types (.global initialized) descriptor.ty := by
    intro previous present
    exact Option.some.inj (present.symm.trans registered)
  have sameTypes : registerRootType types (.global initialized) descriptor.ty = types := by
    funext root
    by_cases same : root = .global initialized
    · subst root
      simp only [registerRootType, ↓reduceIte, registered]
    · simp only [registerRootType, same, ↓reduceIte]
  obtain ⟨after, evaluated, _, post⟩ := bindRoot_freshStored_world config initialized before ambient types liveRoots
    (.global initialized) descriptor.ty stored world compatible
    (world.layouts _ _ registered) represented backed fresh (by intro region member; cases member)
    (by intro act scope id impossible; cases impossible)
    (by
      intro id same outside
      cases same
      have bound := (Array.getElem?_eq_some_iff.mp declared).1
      omega)
  rw [sameTypes] at post
  obtain ⟨result, bound, objects⟩ := bindRoot_objects (.global initialized) (.stored stored) before
  have same := (ExecutionStep.ok.inj (bound.symm.trans evaluated)).2
  subst result
  have present : after.objects.lookup (.global initialized) = some (.stored stored) := by
    simp only [objects, List.lookup, beq_self_eq_true]
  refine ⟨after, evaluated, ⟨post.ownership, ?_, post.globalTypes, post.layouts, post.typeFrontier, post.syntheticFrontier,
    post.heap, post.objectsRegistered, post.ordinalsRegistered, post.backing, post.protections, post.carriers⟩, ?_⟩
  · refine ⟨(Array.getElem?_eq_some_iff.mp declared).1, ?_⟩
    intro id available
    have cases : id < initialized ∨ id = initialized := Nat.lt_succ_iff_lt_or_eq.mp available
    rcases cases with prior | same
    · exact post.globals.2 id prior
    · subst id
      exact ⟨descriptor, .stored stored, declared, present,
        (post.heap _ _ _ registered present).1⟩
  · intro id available
    have cases : id < initialized ∨ id = initialized := Nat.lt_succ_iff_lt_or_eq.mp available
    rcases cases with prior | same
    · exact post.globalLive id prior
    · subst id
      exact Or.inl rfl

#print axioms bindRoot_registeredHeap
#print axioms registerRootType_frontier
#print axioms bindRoot_freshStored_registered
#print axioms registerRootType_layouts
#print axioms bindRoot_freshStored_world
#print axioms bindRoot_freshGlobalStored_world

end Goose.Proofs.ConstructionAcceptedExecution
