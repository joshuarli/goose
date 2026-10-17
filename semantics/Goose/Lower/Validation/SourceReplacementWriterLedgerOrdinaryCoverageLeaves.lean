import Goose.Lower.Validation.SourceReplacementWriterLedgerOrdinaryCoverageLists

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem place_emission_coverage (property : Inst → Prop) (place : Place) (env : LEnv) (before : LS) :
    EmissionCoverage property (.place place) env before := by
  intro neutral children events
  change At property env before (lowerPlace place)
  cases place with
  | var index => exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | global index => exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | deref expression => exact children.at_index 0 rfl
  | field owner index =>
    unfold lowerPlace
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | elem view index origin =>
    unfold lowerPlace
    apply At.bind
    · exact children.at_index 0 rfl
    · apply At.bind
      · exact children.at_index 1 rfl
      · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])

theorem view_emission_coverage (property : Inst → Prop) (view : View) (env : LEnv) (before : LS) :
    EmissionCoverage property (.view view) env before := by
  intro neutral children events
  change At property env before (lowerView view)
  cases view with
  | of place =>
    unfold lowerView
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])
  | val expression =>
    unfold lowerView
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.neutralDef neutral (by intro; simp [NeutralInstruction, WriterInstruction])

theorem bound_emission_coverage (property : Inst → Prop) (bound : Bound) (env : LEnv) (before : LS) :
    EmissionCoverage property (.bound bound) env before := by
  intro neutral children events
  change At property env before (lowerBound bound)
  cases bound with
  | omitted => exact At.pure _ _ _ _
  | expr expression | fromEnd expression =>
    unfold lowerBound
    apply At.bind
    · exact children.at_index 0 rfl
    · exact At.pure _ _ _ _

#print axioms place_emission_coverage
#print axioms view_emission_coverage
#print axioms bound_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
