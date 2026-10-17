import Goose.Lower.Validation.ReplacementIndependence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem replacementApart_of_distinct_slot_type {func : Func} {queries : ReplacementQueries}
    {owner : ValueId} {query : ReplacementRootQuery} {roots : List RootRef} {ownerType : Ty}
    (ownerQuery : queries.value owner = some roots)
    (localTypes : ∀ slot, RootRef.local slot ∈ roots →
      ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = ownerType)
    {slot : SlotId} {storage : GIR.Slot} (storageAt : func.slots[slot]? = some storage)
    (different : storage.ty ≠ ownerType) (addressQuery : ReplacementRootsWithin query [.local slot]) :
    ReplacementApart queries owner query := by
  apply replacementApart_of_source ⟨roots, ownerQuery, List.Subset.refl _⟩ addressQuery
  intro root member address addressMember
  have sameAddress := List.mem_singleton.mp addressMember
  subst address
  cases root with
  | global index => rfl
  | param index => rfl
  | «local» index =>
    have differentSlot : index ≠ slot := by
      intro same
      subst index
      obtain ⟨actual, actualAt, actualType⟩ := localTypes slot member
      have sameStorage := Option.some.inj (actualAt.symm.trans storageAt)
      subst actual
      exact different actualType
    simp [Core.rootsMayOverlap, differentSlot]

theorem replacementApart_of_reference_slot {func : Func} {queries : ReplacementQueries}
    {owner : ValueId} {query : ReplacementRootQuery} {roots : List RootRef} {ownerType : Ty}
    (ownerQuery : queries.value owner = some roots) (ownerNotRef : ownerType.isRefLike = false)
    (localTypes : ∀ slot, RootRef.local slot ∈ roots →
      ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = ownerType)
    {slot : SlotId} {storage : GIR.Slot} (storageAt : func.slots[slot]? = some storage)
    (reference : storage.ty.isRefLike = true) (addressQuery : ReplacementRootsWithin query [.local slot]) :
    ReplacementApart queries owner query := by
  apply replacementApart_of_distinct_slot_type ownerQuery localTypes storageAt ?_ addressQuery
  intro same
  have incompatible := congrArg Ty.isRefLike same
  simp only [reference, ownerNotRef] at incompatible
  contradiction

theorem replacementApart_of_nonowner_slot {func : Func} {queries : ReplacementQueries}
    {owner : ValueId} {query : ReplacementRootQuery} {roots : List RootRef} {ownerType : Ty}
    (ownerQuery : queries.value owner = some roots) (owning : ownerType.ownerElem?.isSome = true)
    (localTypes : ∀ slot, RootRef.local slot ∈ roots →
      ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = ownerType)
    {slot : SlotId} {storage : GIR.Slot} (storageAt : func.slots[slot]? = some storage)
    (nonowner : storage.ty.ownerElem?.isSome = false)
    (addressQuery : ReplacementRootsWithin query [.local slot]) :
    ReplacementApart queries owner query := by
  apply replacementApart_of_distinct_slot_type ownerQuery localTypes storageAt ?_ addressQuery
  intro same
  have incompatible := congrArg (fun type : Ty => type.ownerElem?.isSome) same
  simp only [owning, nonowner] at incompatible
  contradiction

theorem ReplacementInstApart.store_reference_slot {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {queries : ReplacementQueries} {owner address value : ValueId}
    {origin : Option OriginId} {roots : List RootRef} {ownerType : Ty}
    (ownerQuery : queries.value owner = some roots) (ownerNotRef : ownerType.isRefLike = false)
    (localTypes : ∀ slot, RootRef.local slot ∈ roots →
      ∃ storage, func.slots[slot]? = some storage ∧ storage.ty = ownerType)
    {slot : SlotId} {storage : GIR.Slot} (storageAt : func.slots[slot]? = some storage)
    (reference : storage.ty.isRefLike = true)
    (addressQuery : ReplacementRootsWithin (queries.ownerDependencies address) [.local slot]) :
    ReplacementInstApart module types queries owner (.eff (.store address value origin)) := by
  constructor
  · intro operand member _
    simp only [emptyFactSourceOperands, ReplacementContentFlow.Model.accessOperands, List.mem_singleton] at member
    subst operand
    exact replacementApart_of_reference_slot ownerQuery ownerNotRef localTypes storageAt reference addressQuery
  · intro operand member _
    simp [ReplacementContentFlow.Model.loadedResults] at member
  · intro result fn args callOrigin impossible
    cases impossible

#print axioms replacementApart_of_distinct_slot_type
#print axioms replacementApart_of_nonowner_slot
#print axioms replacementApart_of_reference_slot
#print axioms ReplacementInstApart.store_reference_slot

end Goose.Lower.Validation
