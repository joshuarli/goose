import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def RootsRepresent (func : Func) (actual source : List RootRef) : Prop :=
  ∀ root ∈ actual, ∀ concrete ∈ func.expandParameterRoot root, concrete ∈ source

theorem rootsRepresent_empty (func : Func) (source : List RootRef) :
    RootsRepresent func [] source := by
  intro root member
  simp at member

theorem rootsRepresent_local (func : Func) (slot : SlotId) :
    RootsRepresent func [.local slot] [.local slot] := by
  intro root member concrete concreteMember
  have same := List.mem_singleton.mp member
  subst root
  exact concreteMember

theorem rootsRepresent_global (func : Func) (global : GlobalId) :
    RootsRepresent func [.global global] [.global global] := by
  intro root member concrete concreteMember
  have same := List.mem_singleton.mp member
  subst root
  exact concreteMember

theorem rootsRepresent_parameter (func : Func) (index : Nat) :
    RootsRepresent func [.param index] (func.parameterRoots index) := by
  intro root member concrete concreteMember
  have same := List.mem_singleton.mp member
  subst root
  exact concreteMember

theorem rootsRepresent_mono {func : Func} {actual source larger : List RootRef}
    (represented : RootsRepresent func actual source)
    (subset : ∀ root ∈ source, root ∈ larger) : RootsRepresent func actual larger := by
  intro root member concrete concreteMember
  exact subset concrete (represented root member concrete concreteMember)

theorem rootsRepresent_union {func : Func} {left right source : List RootRef}
    (leftBound : RootsRepresent func left source) (rightBound : RootsRepresent func right source) :
    RootsRepresent func (unionRoots left right) source := by
  intro root member
  exact (mem_unionRoots_iff.mp member).elim (leftBound root) (rightBound root)

theorem storageTargets_rootsTargets (func : Func) (roots : List RootRef) :
    func.storageTargets (rootsTargets roots) =
      rootsTargets (roots.flatMap func.expandParameterRoot) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
    cases root <;> simp [rootsTargets, rootTarget, Func.storageTargets,
      Func.expandParameterRoot, List.flatMap_append] at ih ⊢ <;> exact ih

theorem rootsRepresent_targets {func : Func} {actual source : List RootRef}
    (represented : RootsRepresent func actual source) :
    ∀ target ∈ func.storageTargets (rootsTargets actual), target ∈ rootsTargets source := by
  intro target member
  rw [storageTargets_rootsTargets] at member
  obtain ⟨root, rootMember, mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨abstract, abstractMember, concreteMember⟩ := List.mem_flatMap.mp rootMember
  exact List.mem_filterMap.mpr
    ⟨root, represented abstract abstractMember root concreteMember, mapped⟩

def allowedRoots (func : Func) (declared : List RootRef) : List RootRef :=
  (declared.filterMap fun
    | .param _ => none
    | root => some root) ++
  (List.range func.params.length).filterMap fun index =>
    if subsetRoots (func.parameterRoots index) declared then some (.param index) else none

theorem allowedRoots_represent (func : Func) (declared : List RootRef) :
    RootsRepresent func (allowedRoots func declared) declared := by
  intro root member concrete concreteMember
  rcases List.mem_append.mp member with directMember | paramMember
  · obtain ⟨source, sourceMember, mapped⟩ := List.mem_filterMap.mp directMember
    cases source with
    | param index => simp at mapped
    | «local» slot =>
      simp only [Option.some.injEq] at mapped
      subst root
      have same : concrete = .local slot := List.mem_singleton.mp concreteMember
      simpa [same] using sourceMember
    | global global =>
      simp only [Option.some.injEq] at mapped
      subst root
      have same : concrete = .global global := List.mem_singleton.mp concreteMember
      simpa [same] using sourceMember
  · obtain ⟨index, _, mapped⟩ := List.mem_filterMap.mp paramMember
    split at mapped
    · rename_i subset
      simp only [Option.some.injEq] at mapped
      subst root
      exact Core.Sound.subsetRoots_mem subset concrete concreteMember
    · simp at mapped

theorem allowedRoots_complete {func : Func} {declared actual : List RootRef}
    (represented : RootsRepresent func actual declared)
    (parameters : ∀ index, RootRef.param index ∈ actual → index < func.params.length) :
    ∀ root ∈ actual, root ∈ allowedRoots func declared := by
  intro root member
  cases root with
  | «local» slot =>
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    exact ⟨.local slot, represented (.local slot) member (.local slot)
      (by simp [Func.expandParameterRoot]), rfl⟩
  | global global =>
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    exact ⟨.global global, represented (.global global) member (.global global)
      (by simp [Func.expandParameterRoot]), rfl⟩
  | param index =>
    apply List.mem_append_right
    apply List.mem_filterMap.mpr
    refine ⟨index, List.mem_range.mpr (parameters index member), ?_⟩
    have subset : subsetRoots (func.parameterRoots index) declared = true := by
      apply List.all_eq_true.mpr
      intro concrete concreteMember
      simpa using represented (.param index) member concrete concreteMember
    simp [subset]


end Goose.Lower.Validation.SummaryPreservation
