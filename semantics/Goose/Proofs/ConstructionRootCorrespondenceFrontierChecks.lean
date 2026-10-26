import Goose.Proofs.ConstructionRootCorrespondenceScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence.FrontierBoundary
open Goose.Construct
open Goose.Core (RootInst)

private def owner : LocalVar := ⟨"owner", .int .u8, .mutable, 0, 0⟩
private def current : RootInterpretation :=
  ⟨⟨0, 0, #[owner], [], []⟩, 0, fun index root => index = 0 ∧ root = .local 0 0 0⟩

private theorem complete_before : AliasComplete current [] := by
  intro left right root leftInst rightInst
  cases leftInst with
  | global id impossible => exact (Nat.not_lt_zero id impossible).elim
  | static id synthetic =>
    cases rightInst with
    | global id impossible => exact (Nat.not_lt_zero id impossible).elim
    | static id synthetic => exact Or.inl rfl
    | parameter index root supplied => cases supplied.2
  | «local» id descriptor scope declared active => cases active
  | parameter index root supplied =>
    obtain ⟨rfl, rfl⟩ := supplied
    cases rightInst with
    | «local» id descriptor scope declared active => cases active
    | parameter index root supplied =>
      obtain ⟨rfl, equal⟩ := supplied
      exact Or.inl rfl

theorem nextAct_parameter_bounds_allow_scope_alias_failure :
    current.environment.act < 1 ∧
      (∀ index act scope variableId, current.parameters index (.local act scope variableId) → act < 1) ∧
      AliasComplete current [] ∧ ¬ AliasComplete (current.enterScope 0 0) [] := by
  refine ⟨Nat.zero_lt_succ _, ?_, complete_before, ?_⟩
  · intro index act scope variableId supplied
    obtain ⟨rfl, equal⟩ := supplied
    cases equal
    exact Nat.zero_lt_succ _
  · intro complete
    have localRoot : Instantiates (current.enterScope 0 0) (.local 0) (.local 0 0 0) :=
      .local 0 owner 0 rfl rfl
    have parameter : Instantiates (current.enterScope 0 0) (.param 0) (.local 0 0 0) :=
      .parameter 0 _ ⟨rfl, rfl⟩
    have conflict := complete _ _ _ localRoot parameter
    simp only [RootAlias, reduceCtorEq, List.not_mem_nil, or_self] at conflict

theorem parameter_origin_excludes_scope_alias_failure : ¬ RootFrontier current 1 := by
  intro frontier
  exact (Nat.lt_irrefl 0 (frontier.2 0 0 0 0 ⟨rfl, rfl⟩)).elim

end Goose.Proofs.ConstructionRootCorrespondence.FrontierBoundary
