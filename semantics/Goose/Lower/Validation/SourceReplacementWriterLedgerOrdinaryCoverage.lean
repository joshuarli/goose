import Goose.Lower.Validation.SourceReplacementWriterLedgerOrdinaryCoverageLeaves
import Goose.Lower.Validation.CfgReadRecipes

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

private theorem expression_emission_coverage (property : Inst → Prop) (expression : Expr)
    (env : LEnv) (before : LS) (ordinary : OrdinaryFragment (.expression expression)) :
    EmissionCoverage property (.expression expression) env before := by
  intro neutral children events
  change At property env before (lowerExpr expression)
  cases expression with
  | lit integer value => exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | bool value => exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | read place =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
      · apply At.bind
        · exact At.of_blocks (recordReadValueRootRecipe_tables _ _ _ _).1
        · exact At.pure _ _ _ _
  | ref mutability place =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutral neutral (neutral_borrowTo _ _)
  | slice mutability view low high origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact children.at_index 1 rfl
      · apply At.bind
        · exact children.at_index 2 rfl
        · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | len view =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | un op expression origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact At.neutral neutral (neutral_intTyOf _)
      · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | bin op left right origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact children.at_index 1 rfl
      · apply At.bind
        · exact At.neutral neutral (neutral_intTyOf _)
        · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | cmp op left right =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact children.at_index 1 rfl
      · apply At.bind
        · exact At.neutral neutral (neutral_valTy _)
        · split <;> exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | not expression =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | conv kind target expression origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact At.neutral neutral (neutral_intTyOf _)
      · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | call function arguments origin =>
    unfold lowerExpr
    apply At.bind
    · exact argumentChildren_covered neutral children.rows
    · apply At.bind
      · apply events.definition
        intro live
        simp only [Fragment.emissions, definitionEmission, live, ite_true, List.mem_singleton]
      · apply At.bind
        · exact At.of_blocks rfl
        · split
          · apply At.bind
            · exact At.term .unreachable neutral
            · exact At.pure _ _ _ _
          · exact At.pure _ _ _ _
  | push place expression origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact children.at_index 1 rfl
      · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | pop place origin =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | arrLit type expressions | structLit type expressions =>
    unfold lowerExpr
    apply At.bind
    · exact expressionChildren_covered children.rows
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | fill type expression =>
    unfold lowerExpr
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | and left right => cases ordinary
  | or left right => cases ordinary
  | ifE condition yes no => cases ordinary
  | blockE block => cases ordinary

theorem ordinary_emission_coverage (property : Inst → Prop) (fragment : Fragment) (env : LEnv) (before : LS)
    (ordinary : OrdinaryFragment fragment) : EmissionCoverage property fragment env before := by
  cases fragment with
  | expression expression => exact expression_emission_coverage property expression env before ordinary
  | place place => exact place_emission_coverage property place env before
  | view view => exact view_emission_coverage property view env before
  | bound bound => exact bound_emission_coverage property bound env before
  | statement loop statement => cases ordinary
  | block loop bindings want block => cases ordinary

#print axioms ordinary_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
