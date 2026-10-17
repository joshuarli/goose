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

end Goose.Lower.Validation.SummaryPreservation
