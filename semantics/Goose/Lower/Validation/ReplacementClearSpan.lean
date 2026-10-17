import Goose.Lower.Validation.ReplacementIndependence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem replacementTrace_to_replace {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {owner run : ValueId} {origin : Option OriginId}
    {insts : List Inst}
    (apart : ∀ inst ∈ insts, ReplacementInstApart module types queries owner inst)
    (noReplacements : ∀ inst ∈ insts, ∀ target value tag, inst ≠ .eff (.replace target value tag))
    (ownerType : ∃ element, ownerTy types owner = some (.grow element) ∨
      ownerTy types owner = some (.growshrink element))
    (fresh : valid[run]? = some true) {facts : List ValueId} (cleared : owner ∈ facts) :
    ReplacementTrace module types queries valid facts (insts ++ [.eff (.replace owner run origin)]) := by
  induction insts generalizing facts with
  | nil =>
    apply ReplacementTrace.cons
    · intro target value tag equal
      cases equal
      exact ⟨ownerType, fresh, cleared⟩
    · exact .nil _
  | cons inst rest ih =>
    apply ReplacementTrace.cons
    · intro target value tag equal
      exact False.elim (noReplacements inst (by simp) target value tag equal)
    · apply ih
      · intro next member
        exact apart next (by simp [member])
      · intro next member
        exact noReplacements next (by simp [member])
      · exact transferEmptyInst_retains_of_apart (apart inst (by simp)) cleared

theorem replacementTrace_clear_span {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {owner run : ValueId}
    {clearOrigin replaceOrigin : Option OriginId} {insts : List Inst}
    (apart : ∀ inst ∈ insts, ReplacementInstApart module types queries owner inst)
    (noReplacements : ∀ inst ∈ insts, ∀ target value tag, inst ≠ .eff (.replace target value tag))
    (ownerType : ∃ element, ownerTy types owner = some (.grow element) ∨
      ownerTy types owner = some (.growshrink element))
    (fresh : valid[run]? = some true) (facts : List ValueId) :
    ReplacementTrace module types queries valid facts
      (.eff (.clear owner clearOrigin) :: insts ++ [.eff (.replace owner run replaceOrigin)]) := by
  apply ReplacementTrace.cons
  · intro target value tag equal
    cases equal
  · exact replacementTrace_to_replace apart noReplacements ownerType fresh
      (transferEmptyInst_clear_has_owner module types queries facts owner clearOrigin)

end Goose.Lower.Validation
