import Goose.Lower.Validation.OriginPreservation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Except ε (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    apply inductionHypothesis
    intro next member
    exact checked next (by simp [member])

theorem checkGlobal_origin_bound {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : Core.checkGlobal module index global = .ok ()) : global.org < module.origins.size := by
  by_cases bound : global.org < module.origins.size
  · exact bound
  · simp only [Core.checkGlobal, bound, ite_false] at checked
    simp [chk] at checked

theorem validate_global_checks {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (lookup : module.globals[index]? = some global) :
    Core.checkGlobal module index global = .ok () := by
  unfold Core.validate at accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, globals, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  have bound : index < module.globals.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have checked := (Core.Sound.forAll_ok _ _).mp globals index (List.mem_range.mpr bound)
  simpa only [lookup] using checked

theorem lower_checkEntryAndGlobals {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    checkEntryAndGlobals (lower module) = .ok () := by
  obtain ⟨ctx, impl, ctxLookup, implLookup, params, results⟩ :=
    (Core.Sound.validate_modOk module accepted).entry
  have noParams : impl.params.toList = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa only [Array.length_toList] using params
  have entry : (lower module).funcs[(lower module).entry]? =
      some (lowerImplAt module ctx.impl impl) := by
    simp only [lower, ctxLookup, Option.map_some, Option.getD_some, Array.getElem?_mapIdx, implLookup]
  have empty : ((lowerImplAt module ctx.impl impl).params.isEmpty &&
      (lowerImplAt module ctx.impl impl).results.isEmpty) = true := by
    simp only [lowerImplAt, noParams, results, List.map_nil, List.isEmpty_nil, Bool.and_true]
  unfold checkEntryAndGlobals
  rw [entry]
  simp only [empty, ite_true, pure, Except.pure, bind, Except.bind]
  rw [← Array.forIn_toList]
  suffices loop : forIn (lower module).globals.toList PUnit.unit _ =
      (Except.ok PUnit.unit : Except Violation PUnit) by
    rw [loop]
  apply forIn_unit_ok
  intro lowered member
  change lowered ∈ (module.globals.map (lowerGlobal module)).toList at member
  simp only [Array.toList_map, List.mem_map] at member
  obtain ⟨global, globalMember, rfl⟩ := member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp globalMember)
  have bound := checkGlobal_origin_bound (validate_global_checks accepted lookup)
  simp [lowerGlobal, lower, bound, bind]

end Goose.Lower.Validation
