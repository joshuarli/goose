import Goose.Lower.Validation.ScopeFlowFinish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem scope_sourceChecks {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (∀ impl ∈ module.impls.toList, checkImpl module impl = .ok ()) ∧
      (∀ index global, module.globals[index]? = some global → checkGlobal module index global = .ok ()) ∧
      (∀ context ∈ module.contexts.toList, checkContext module context = .ok ()) := by
  unfold Core.validate at accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, globals, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, implementations, accepted⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, contexts, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp accepted
  refine ⟨(Core.Sound.forAll_ok _ _).mp implementations, ?_, (Core.Sound.forAll_ok _ _).mp contexts⟩
  intro index global lookup
  have bound : index < module.globals.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have checked := (Core.Sound.forAll_ok _ _).mp globals index (List.mem_range.mpr bound)
  simpa only [lookup] using checked

theorem lower_func_scopeGraph {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {func : Func}
    (lookup : (lower module).funcs[index]? = some func) : Nonempty (ScopeGraph func) := by
  obtain ⟨implementations, globals, contexts⟩ := scope_sourceChecks accepted
  cases contextAt : module.contexts[index]? with
  | none => simp [lower, Array.getElem?_map, contextAt] at lookup
  | some context =>
    have checked := contexts context (Array.mem_toList_iff.mpr (Array.mem_of_getElem? contextAt))
    cases implAt : module.impls[context.impl]? with
    | none => simp [checkContext, implAt, reject] at checked
    | some impl =>
      have lowered := lower_func_at contextAt implAt
      have same : lowerContextAt module context impl = func := Option.some.inj (lowered.symm.trans lookup)
      rw [← same]
      exact lowerContextAt_scopeGraph
        (implementations impl (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))) context

theorem lower_global_scopeGraph {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : GIR.Global}
    (lookup : (lower module).globals[index]? = some global) : Nonempty (ScopeGraph global.init) := by
  obtain ⟨implementations, globals, contexts⟩ := scope_sourceChecks accepted
  cases globalAt : module.globals[index]? with
  | none => simp [lower, Array.getElem?_map, globalAt] at lookup
  | some source =>
    have same : lowerGlobal module source = global := by
      simpa only [lower, Array.getElem?_map, globalAt, Option.map_some, Option.some.injEq] using lookup
    rw [← same]
    exact lowerGlobal_scopeGraph (globals index source globalAt)

theorem lower_labelled_scopeGraph {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {label : String} {func : Func}
    (member : (label, func) ∈ (lower module).labelled) : Nonempty (ScopeGraph func) := by
  simp only [GIR.Module.labelled, List.mem_append, List.mem_map] at member
  rcases member with ⟨function, member, same⟩ | ⟨global, member, same⟩
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact lower_func_scopeGraph accepted lookup
  · obtain ⟨_, rfl⟩ := Prod.mk.inj same
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact lower_global_scopeGraph accepted lookup

theorem lower_walkScopes {module : Core.Module} (accepted : Core.validate module = .ok ())
    (info : FnInfo) (member : info ∈ (lower module).infos) :
    (walkScopes info.label info.f).scopes = none := by
  simp only [GIR.Module.infos, List.mem_map] at member
  obtain ⟨⟨label, func⟩, member, same⟩ := member
  cases same
  obtain ⟨graph⟩ := lower_labelled_scopeGraph accepted member
  exact graph.walkScopes label

theorem lower_checkScopes {module : Core.Module} (accepted : Core.validate module = .ok ()) :
    (checkAll ((lower module).infos.map fun info => walkScopes info.label info.f) fun walk => do
      if let some message := walk.scopes then violation .v040 message) = .ok () := by
  have clean : ∀ walk ∈ ((lower module).infos.map fun info => walkScopes info.label info.f),
      walk.scopes = none := by
    intro walk member
    obtain ⟨info, infoMember, rfl⟩ := List.mem_map.mp member
    exact lower_walkScopes accepted info infoMember
  generalize ((lower module).infos.map fun info => walkScopes info.label info.f) = walks at clean ⊢
  induction walks with
  | nil => rfl
  | cons walk rest inductionHypothesis =>
    have none := clean walk (by simp)
    simp only [checkAll, none, bind, Except.bind, pure, Except.pure]
    apply inductionHypothesis
    intro next member
    exact clean next (by simp [member])

end Goose.Lower.Validation
