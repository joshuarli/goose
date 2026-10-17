import Goose.Core.Sound.Frame
import Goose.GIR.Effects
import Goose.Lower.Frag
import Goose.GIR.RootSeeds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem seed_fold_contains (slot : Nat) (root : RootRef) (rows : List (Nat × List RootRef))
    (initial : List RootRef)
    (present : root ∈ initial ∨ ∃ row ∈ rows, row.1 = slot ∧ root ∈ row.2) :
    root ∈ rows.foldl (fun roots row => if row.1 == slot then unionRoots roots row.2 else roots) initial := by
  induction rows generalizing initial with
  | nil => simpa using present
  | cons row rest ih =>
    apply ih
    rcases present with old | ⟨selected, member, same, included⟩
    · left
      dsimp only
      split
      · exact unionRoots_left _ _ _ old
      · exact old
    · rcases List.mem_cons.mp member with identity | later
      · subst selected
        left
        simp only [same, beq_self_eq_true, ite_true]
        exact unionRoots_right _ _ _ included
      · exact Or.inr ⟨selected, later, same, included⟩

theorem slotRootSeeds_contains {func : Func} {slot : SlotId} {declared : List RootRef}
    (bounded : slot < func.slots.size)
    (row : (slot, declared) ∈ func.roots.slots.getD #[]) :
    ∀ root ∈ declared, root ∈ rootsAt func.slotRootSeeds slot := by
  intro root member
  simp only [rootsAt, Func.slotRootSeeds, Array.getElem?_mapIdx]
  obtain ⟨descriptor, found⟩ := Option.isSome_iff_exists.mp
    (show (func.slots[slot]?).isSome = true by simp [bounded])
  simp only [found, Option.map_some, Option.getD_some]
  rw [← Array.foldl_toList]
  exact seed_fold_contains slot root _ [] (Or.inr ⟨(slot, declared), Array.mem_toList_iff.mpr row, rfl, member⟩)

theorem lowerContext_slot_seed_ceiling {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : VarId} {localVar : LocalVar} {declared : List RootRef}
    (variableRow : impl.vars[slot]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (ordinary : localVar.ty.isRefSlice = false)
    (annotation : (slot, declared) ∈ ctx.varRoots) :
    ∀ root ∈ lowerContextRootCeiling ctx impl declared,
      root ∈ rootsAt (lowerContextAt module ctx impl).slotRootSeeds slot := by
  have metadata : (slot, lowerContextRootCeiling ctx impl declared) ∈
      (lowerContextAt module ctx impl).roots.slots.getD #[] := by
    change (slot, lowerContextRootCeiling ctx impl declared) ∈ (ctx.varRoots.filterMap _).toArray
    apply Array.mem_toList_iff.mp
    apply List.mem_filterMap.mpr
    refine ⟨(slot, declared), annotation, ?_⟩
    simp [variableRow, reference, ordinary]
  apply slotRootSeeds_contains (slot := slot) ?_ metadata
  simpa [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv] using
    (Array.getElem?_eq_some_iff.mp variableRow).1

theorem lowerContext_slot_seed_source {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : VarId} {localVar : LocalVar} {declared : List RootRef}
    (variableRow : impl.vars[slot]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (ordinary : localVar.ty.isRefSlice = false)
    (annotation : (slot, declared) ∈ ctx.varRoots) :
    ∀ root ∈ declared, root ∈ rootsAt (lowerContextAt module ctx impl).slotRootSeeds slot := by
  intro root member
  exact lowerContext_slot_seed_ceiling variableRow reference ordinary annotation root
    (unionRoots_left _ _ _ member)

theorem lowerContext_slot_seed_parameter {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : VarId} {localVar : LocalVar} {declared : List RootRef} {parameter : Param}
    (variableRow : impl.vars[slot]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (parameterRow : impl.params[slot]? = some parameter) (aligned : parameter.var = slot)
    (annotation : (slot, declared) ∈ ctx.varRoots) :
    RootRef.param slot ∈ rootsAt (lowerContextAt module ctx impl).slotRootSeeds slot := by
  have refLike : localVar.ty.isRefLike = true := by
    cases shape : localVar.ty <;> simp_all [Ty.isRefSlice, Ty.isRefLike]
  have metadata : (slot, [.param slot]) ∈
      (lowerContextAt module ctx impl).roots.slots.getD #[] := by
    change (slot, [RootRef.param slot]) ∈ (ctx.varRoots.filterMap _).toArray
    apply Array.mem_toList_iff.mp
    apply List.mem_filterMap.mpr
    refine ⟨(slot, declared), annotation, ?_⟩
    simp [variableRow, refLike, reference, parameterRow, aligned]
  apply slotRootSeeds_contains (slot := slot) ?_ metadata (.param slot) (by simp)
  simpa [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv] using
    (Array.getElem?_eq_some_iff.mp variableRow).1

#print axioms lowerContext_slot_seed_parameter
#print axioms slotRootSeeds_contains
#print axioms lowerContext_slot_seed_ceiling
#print axioms lowerContext_slot_seed_source

end Goose.Lower.Validation.ReplacementContentFlowSource
