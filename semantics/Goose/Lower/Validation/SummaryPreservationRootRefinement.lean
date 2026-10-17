import Goose.Lower.Validation.SummaryPreservationAllowedResults
import Goose.GIR.RootBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

abbrev RootsRefine := Goose.GIR.RootsRefine

theorem RootsRefine.refl (func : Func) (roots : List RootRef) : RootsRefine func roots roots :=
  fun _ member => Or.inl member

theorem RootsRefine.of_represented {func : Func} {actual source : List RootRef}
    (represented : RootsRepresent func actual source) : RootsRefine func actual source :=
  fun root member => Or.inr (represented root member)

theorem RootsRefine.source_mono {func : Func} {actual source larger : List RootRef}
    (prior : RootsRefine func actual source) (subset : ∀ root ∈ source, root ∈ larger) :
    RootsRefine func actual larger := by
  intro root member
  rcases prior root member with literal | expanded
  · exact Or.inl (subset root literal)
  · exact Or.inr (fun concrete concreteMember => subset concrete (expanded concrete concreteMember))

theorem RootsRefine.union {func : Func} {left right source : List RootRef}
    (leftBound : RootsRefine func left source) (rightBound : RootsRefine func right source) :
    RootsRefine func (unionRoots left right) source := by
  intro root member
  exact (mem_unionRoots_iff.mp member).elim (leftBound root) (rightBound root)

theorem RootsRefine.expanded {func : Func} {actual source : List RootRef}
    (closed : ParameterRootsClosed func) (refined : RootsRefine func actual source) :
    ∀ root ∈ actual, ∀ concrete ∈ func.expandParameterRoot root,
      concrete ∈ source.flatMap func.expandParameterRoot := by
  intro root member concrete concreteMember
  rcases refined root member with literal | expanded
  · exact List.mem_flatMap.mpr ⟨root, literal, concreteMember⟩
  · cases root with
    | «local» slot =>
      have same : concrete = .local slot := List.mem_singleton.mp concreteMember
      subst concrete
      exact List.mem_flatMap.mpr ⟨.local slot, expanded _ (by simp [Func.expandParameterRoot]),
        by simp [Func.expandParameterRoot]⟩
    | global global =>
      have same : concrete = .global global := List.mem_singleton.mp concreteMember
      subst concrete
      exact List.mem_flatMap.mpr ⟨.global global, expanded _ (by simp [Func.expandParameterRoot]),
        by simp [Func.expandParameterRoot]⟩
    | param index =>
      rcases closed index concrete concreteMember with own | ⟨global, same⟩
      · subst concrete
        exact List.mem_flatMap.mpr ⟨.param index, expanded _ concreteMember, concreteMember⟩
      · subst concrete
        exact List.mem_flatMap.mpr ⟨.global global, expanded _ concreteMember,
          by simp [Func.expandParameterRoot]⟩

theorem RootsRefine.targets {func : Func} {actual source : List RootRef}
    (closed : ParameterRootsClosed func) (refined : RootsRefine func actual source) :
    ∀ target ∈ func.storageTargets (rootsTargets actual),
      target ∈ func.storageTargets (rootsTargets source) := by
  intro target member
  rw [storageTargets_rootsTargets] at member ⊢
  obtain ⟨concrete, concreteMember, mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨root, rootMember, expandedMember⟩ := List.mem_flatMap.mp concreteMember
  exact List.mem_filterMap.mpr
    ⟨concrete, RootsRefine.expanded closed refined root rootMember concrete expandedMember, mapped⟩

end Goose.Lower.Validation.SummaryPreservation
