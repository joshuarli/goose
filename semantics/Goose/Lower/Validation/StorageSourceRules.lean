import Goose.Lower.Validation.SourceStorage
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageAuthority (profile : ArtifactProfile) (types : Array (Option VTy)) : Inst → Prop
  | .def _ (.load owner) => ∃ mu ty, types[owner]? = some (some (.data (.ref mu ty))) ∧
      (ty.readable = true ∨ ty.isRefSlice = true)
  | .eff (.store owner _ _) => ∃ ty, types[owner]? = some (some (.data (.ref .mutable ty))) ∧
      ty.readable = true
  | .def _ (.push owner _ _) | .eff (.append owner _ _) =>
      ∃ mu ty, types[owner]? = some (some (.data (.ref mu ty))) ∧
        (mu = .mutable ∨ ty.ownerElem?.isSome = true)
  | .def _ (.pop owner _) | .eff (.popN owner _ _) | .eff (.resize owner _ _ _) | .eff (.clear owner _) =>
      ∃ mu ty, types[owner]? = some (some (.data (.ref mu ty))) ∧
        (mu = .mutable ∨ profile = .shrink ∧ ty.ownerElem?.isSome = true)
  | .eff (.replace owner _ _) =>
      ∃ mu ty, types[owner]? = some (some (.data (.ref mu ty))) ∧
        (mu = .mutable ∨ profile = .shrink ∧ ∃ element, ty = .grow element ∨ ty = .growshrink element)
  | _ => True

theorem StorageAuthority.retained {profile : ArtifactProfile} {before after : Array (Option VTy)}
    {instruction : Inst} (types : ∀ (value : ValueId) (ty : VTy), before[value]? = some (some ty) → after[value]? = some (some ty))
    (certificate : StorageAuthority profile before instruction) : StorageAuthority profile after instruction := by
  cases instruction with
  | «def» value op =>
      cases op <;> simp only [StorageAuthority] at certificate ⊢ <;> try exact certificate
      all_goals
        obtain ⟨mu, ty, row, allowed⟩ := certificate
        exact ⟨mu, ty, types _ _ row, allowed⟩
  | eff effect =>
      cases effect <;> simp only [StorageAuthority] at certificate ⊢ <;> try exact certificate
      case store owner value origin =>
        obtain ⟨ty, row, allowed⟩ := certificate
        exact ⟨ty, types _ _ row, allowed⟩
      all_goals
        obtain ⟨mu, ty, row, allowed⟩ := certificate
        exact ⟨mu, ty, types _ _ row, allowed⟩
  | term term => exact certificate

theorem StorageAuthority.rule {profile : ArtifactProfile} {types : Array (Option VTy)} {instruction : Inst}
    (certificate : StorageAuthority profile types instruction) : StorageRule profile types instruction := by
  constructor
  · intro result owner mu ty same typed
    subst instruction
    obtain ⟨actualMu, actualTy, row, allowed⟩ := certificate
    have equality := Option.some.inj (Option.some.inj (row.symm.trans typed))
    cases equality
    exact allowed
  · intro owner value origin mu ty same typed
    subst instruction
    obtain ⟨actualTy, row, allowed⟩ := certificate
    have equality := Option.some.inj (Option.some.inj (row.symm.trans typed))
    cases equality
    exact ⟨rfl, allowed⟩
  · intro owner mu ty growing typed
    cases growing <;>
      obtain ⟨actualMu, actualTy, row, allowed⟩ := certificate <;>
      have equality := Option.some.inj (Option.some.inj (row.symm.trans typed)) <;>
      cases equality <;> exact allowed
  · intro owner mu ty shrinking typed
    cases shrinking <;>
      obtain ⟨actualMu, actualTy, row, allowed⟩ := certificate <;>
      have equality := Option.some.inj (Option.some.inj (row.symm.trans typed)) <;>
      cases equality <;> exact allowed
  · intro owner value origin mu ty same typed
    subst instruction
    obtain ⟨actualMu, actualTy, row, allowed⟩ := certificate
    have equality := Option.some.inj (Option.some.inj (row.symm.trans typed))
    cases equality
    exact allowed

#print axioms StorageAuthority.retained
#print axioms StorageAuthority.rule

end Goose.Lower.Validation
