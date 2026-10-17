import Goose.Lower.Validation.SummaryPreservationLowerIfE
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_ifE_children {env : TEnv} {condition : Expr} {yes no : Core.Block}
    {start finish : Nat} {type : Ty}
    (source : tyExpr env (.ifE condition yes no) start = .ok (type, finish)) :
    ∃ conditionCounter yesCounter,
      tyExpr env condition start = .ok (.bool, conditionCounter) ∧
      tyBlock (exprEnv env) [] yes conditionCounter = .ok (type, yesCounter) ∧
      tyBlock (exprEnv env) [] no yesCounter = .ok (type, finish) := by
  simp only [tyExpr] at source
  inv at source
  obtain ⟨conditionType, conditionCounter, conditionTyped, conditionBool, yesType, yesCounter,
    yesTyped, noType, noCounter, noTyped, same, typeEq, finishEq⟩ := source
  have equal : yesType = noType := by simpa using same
  subst conditionType
  subst type
  subst finish
  subst noType
  exact ⟨conditionCounter, yesCounter, conditionTyped, yesTyped, noTyped⟩

theorem rpExpr_ifE_children {env : PEnv} {condition : Expr} {yes no : Core.Block}
    {before after : RState} {sourceRoots : List RootRef}
    (source : rpExpr env (.ifE condition yes no) before = .ok (sourceRoots, after)) :
    ∃ conditionRoots conditionState yesRoots yesRange yesState noRoots noRange,
      rpExpr env condition before = .ok (conditionRoots, conditionState) ∧
      rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState) ∧
      rpBlockValue env [] no yesState = .ok ((noRoots, noRange), after) ∧
      sourceRoots = unionRoots yesRoots noRoots := by
  obtain ⟨conditionRoots, conditionState, conditionReplay, tail⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨⟨yesRoots, yesRange⟩, yesState, yesReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨⟨noRoots, noRange⟩, noState, noReplay, result⟩ := (st_bind_ok _ _ _ _).mp tail
  have equal := (st_pure_ok _ _ _).mp result
  cases equal
  exact ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, noRoots, noRange,
    conditionReplay, yesReplay, noReplay, rfl⟩

end Goose.Lower.Validation.SummaryPreservation
