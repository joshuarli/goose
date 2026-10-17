import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive GrowingStorage : ValueId → Inst → Prop
  | push (result owner value origin) : GrowingStorage owner (.def result (.push owner value origin))
  | append (owner value origin) : GrowingStorage owner (.eff (.append owner value origin))

inductive ShrinkingStorage : ValueId → Inst → Prop
  | pop (result owner origin) : ShrinkingStorage owner (.def result (.pop owner origin))
  | popN (owner count origin) : ShrinkingStorage owner (.eff (.popN owner count origin))
  | resize (owner count value origin) : ShrinkingStorage owner (.eff (.resize owner count value origin))
  | clear (owner origin) : ShrinkingStorage owner (.eff (.clear owner origin))

structure StorageRule (profile : ArtifactProfile) (types : Array (Option VTy))
    (instruction : Inst) : Prop where
  load : ∀ result owner mu ty, instruction = .def result (.load owner) →
    types[owner]? = some (some (.data (.ref mu ty))) → ty.readable = true ∨ ty.isRefSlice = true
  store : ∀ owner value origin mu ty, instruction = .eff (.store owner value origin) →
    types[owner]? = some (some (.data (.ref mu ty))) → mu = .mutable ∧ ty.readable = true
  grow : ∀ owner mu ty, GrowingStorage owner instruction →
    types[owner]? = some (some (.data (.ref mu ty))) → mu = .mutable ∨ ty.ownerElem?.isSome = true
  shrink : ∀ owner mu ty, ShrinkingStorage owner instruction →
    types[owner]? = some (some (.data (.ref mu ty))) →
      mu = .mutable ∨ profile = .shrink ∧ ty.ownerElem?.isSome = true
  replace : ∀ owner value origin mu ty, instruction = .eff (.replace owner value origin) →
    types[owner]? = some (some (.data (.ref mu ty))) →
      mu = .mutable ∨ profile = .shrink ∧ ∃ element, ty = .grow element ∨ ty = .growshrink element

theorem storage_ref_lookup {types : Array (Option VTy)} {owner : ValueId} {mu : Mutability} {ty : Ty}
    (typed : (match types[owner]? with
      | some (some (.data (.ref mutability referent))) => some (mutability, referent)
      | _ => none) = some (mu, ty)) : types[owner]? = some (some (.data (.ref mu ty))) := by
  split at typed <;> simp_all

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, checked item (by simp)]
    exact ih (fun next member => checked next (by simp [member]))

private theorem forIn_result_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (result : β) (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    (forIn items PUnit.unit body >>= fun _ => pure result : Check β) = .ok result := by
  rw [forIn_unit_ok checked]
  rfl

theorem checkStorage_of_rules {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    (rules : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, StorageRule module.profile types inst)
    (label : String) : checkStorage module label func types = .ok () := by
  unfold checkStorage
  dsimp only
  rw [← Array.forIn_toList]
  apply forIn_result_ok
  intro block blockMember
  apply forIn_result_ok
  intro inst instMember
  have rule := rules block blockMember inst instMember
  cases inst with
  | «def» result op =>
    cases op <;> simp only <;> try rfl
    case load owner =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.load result owner mu ty rfl typed
      rcases allowed with readable | slice <;> simp_all [pure, Except.pure]
    case push owner value origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.grow owner mu ty (.push result owner value origin) typed
      rcases allowed with mutable | owning <;> simp_all [pure, Except.pure]
    case pop owner origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.shrink owner mu ty (.pop result owner origin) typed
      rcases allowed with mutable | ⟨profile, owning⟩ <;> simp_all [pure, Except.pure]
  | eff effect =>
    cases effect <;> simp only <;> try rfl
    case store owner value origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      obtain ⟨mutable, readable⟩ := rule.store owner value origin mu ty rfl typed
      simp [mutable, readable, pure, Except.pure]
    case append owner value origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.grow owner mu ty (.append owner value origin) typed
      rcases allowed with mutable | owning <;> simp_all [pure, Except.pure]
    case popN owner count origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.shrink owner mu ty (.popN owner count origin) typed
      rcases allowed with mutable | ⟨profile, owning⟩ <;> simp_all [pure, Except.pure]
    case resize owner count value origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.shrink owner mu ty (.resize owner count value origin) typed
      rcases allowed with mutable | ⟨profile, owning⟩ <;> simp_all [pure, Except.pure]
    case clear owner origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.shrink owner mu ty (.clear owner origin) typed
      rcases allowed with mutable | ⟨profile, owning⟩ <;> simp_all [pure, Except.pure]
    case replace owner value origin =>
      split <;> try rfl
      rename_i mu ty typed
      have typed := storage_ref_lookup typed
      have allowed := rule.replace owner value origin mu ty rfl typed
      rcases allowed with mutable | ⟨profile, element, shape | shape⟩ <;>
        simp_all [pure, Except.pure]
  | term term => rfl

end Goose.Lower.Validation
