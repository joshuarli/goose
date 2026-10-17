import Goose.GIR.RootBounds

namespace Goose.GIR

open Goose.Core

theorem RootsRefine.refl (func : Func) (roots : List RootRef) : RootsRefine func roots roots :=
  fun _ member => Or.inl member

theorem RootsRefine.source_mono {func : Func} {actual source larger : List RootRef}
    (prior : RootsRefine func actual source) (subset : source ⊆ larger) :
    RootsRefine func actual larger := by
  intro root member
  rcases prior root member with literal | expanded
  · exact Or.inl (subset literal)
  · exact Or.inr (fun concrete concreteMember => subset (expanded concrete concreteMember))

theorem RootsRefine.actual_mono {func : Func} {actual smaller source : List RootRef}
    (prior : RootsRefine func actual source) (subset : smaller ⊆ actual) :
    RootsRefine func smaller source := fun root member => prior root (subset member)

theorem RootsRefine.trans {func : Func} {before middle after : List RootRef}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (first : RootsRefine func before middle) (second : RootsRefine func middle after) :
    RootsRefine func before after := by
  intro root member
  rcases first root member with literal | expanded
  · exact second root literal
  · cases root with
    | «local» slot => exact second (.local slot) (expanded _ (by simp [Func.expandParameterRoot]))
    | global global => exact second (.global global) (expanded _ (by simp [Func.expandParameterRoot]))
    | param index =>
        by_cases self : RootRef.param index ∈ func.parameterRoots index
        · exact second (.param index) (expanded _ self)
        · refine Or.inr ?_
          intro concrete concreteMember
          rcases closed index concrete concreteMember with own | ⟨global, same⟩
          · subst concrete
            exact False.elim (self concreteMember)
          · subst concrete
            rcases second (.global global) (expanded _ concreteMember) with direct | represented
            · exact direct
            · exact represented _ (by simp [Func.expandParameterRoot])

theorem RootsRefine.expanded {func : Func} {actual source : List RootRef}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (refined : RootsRefine func actual source) :
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

theorem RootsRefine.map {caller callee : Func} {actual source : List RootRef}
    (mapped : RootRef → List RootRef)
    (parameterContracts : ∀ index, RootsRefine caller (mapped (.param index))
      ((callee.parameterRoots index).flatMap mapped))
    (bounded : RootsRefine callee actual source) :
    RootsRefine caller (actual.flatMap mapped) (source.flatMap mapped) := by
  intro root member
  obtain ⟨before, beforeMember, mappedMember⟩ := List.mem_flatMap.mp member
  rcases bounded before beforeMember with literal | expanded
  · exact Or.inl (List.mem_flatMap.mpr ⟨before,literal,mappedMember⟩)
  · cases before with
    | «local» slot =>
        exact Or.inl (List.mem_flatMap.mpr
          ⟨.local slot,expanded _ (by simp [Func.expandParameterRoot]),mappedMember⟩)
    | global global =>
        exact Or.inl (List.mem_flatMap.mpr
          ⟨.global global,expanded _ (by simp [Func.expandParameterRoot]),mappedMember⟩)
    | param index =>
        exact ((parameterContracts index).source_mono (by
          intro concrete included
          obtain ⟨parameterRoot, parameterMember, mappedMember⟩ := List.mem_flatMap.mp included
          exact List.mem_flatMap.mpr ⟨parameterRoot,expanded _ parameterMember,mappedMember⟩)) root mappedMember

end Goose.GIR
