import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageEach
import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageStatements
import Goose.Lower.Validation.SourceReplacementWriterLedgerOrdinaryCoverage

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem print_emission_coverage (property : Inst → Prop) (env : LEnv) (before : LS)
    (loop : Option LoopCtx) (arguments : List PrintArg) (origin : OriginId) :
    EmissionCoverage property (.statement loop (.print arguments origin)) env before := by
  intro neutral children events
  exact At.bind (printChildren_covered children.rows)
    (At.neutralEffect neutral (by simp [NeutralInstruction,WriterInstruction]))

theorem fragment_emission_coverage (property : Inst → Prop) (fragment : Fragment)
    (env : LEnv) (before : LS) : EmissionCoverage property fragment env before := by
  cases fragment with
  | expression expression =>
    cases expression with
    | and left right => exact and_emission_coverage _ _ _ _ _
    | or left right => exact or_emission_coverage _ _ _ _ _
    | ifE condition yes no => exact ifExpression_emission_coverage _ _ _ _ _ _
    | blockE block => exact blockExpression_emission_coverage _ _ _ _
    | _ => exact ordinary_emission_coverage _ _ _ _ (by trivial)
  | statement loop statement =>
    cases statement with
    | letS => exact let_emission_coverage _ _ _ _ _ _ _
    | assign => exact assign_emission_coverage _ _ _ _ _ _ _
    | assignOp => exact assignOp_emission_coverage _ _ _ _ _ _ _ _
    | rebind => exact rebind_emission_coverage _ _ _ _ _ _ _
    | expr => exact expressionStatement_emission_coverage _ _ _ _ _ _
    | append => exact append_emission_coverage _ _ _ _ _ _ _
    | popN => exact popN_emission_coverage _ _ _ _ _ _ _
    | resize => exact resize_emission_coverage _ _ _ _ _ _ _ _
    | clear => exact clear_emission_coverage _ _ _ _ _ _
    | assignWhole => exact assignWhole_emission_coverage _ _ _ _ _ _ _
    | ifS => exact ifStatement_emission_coverage _ _ _ _ _ _ _ _
    | «while» => exact while_emission_coverage _ _ _ _ _ _ _
    | forRange => exact range_emission_coverage _ _ _ _ _ _ _ _ _
    | forEach => exact each_emission_coverage _ _ _ _ _ _ _ _ _ _
    | ret => exact return_emission_coverage _ _ _ _ _ _
    | brk => exact break_emission_coverage _ _ _ _ _
    | cont => exact continue_emission_coverage _ _ _ _ _
    | print => exact print_emission_coverage _ _ _ _ _ _
    | assertS => exact assert_emission_coverage _ _ _ _ _ _
    | abort => exact abort_emission_coverage _ _ _ _ _ _
    | exit => exact exit_emission_coverage _ _ _ _ _ _
  | block => exact block_emission_coverage _ _ _ _ _ _ _
  | _ => exact ordinary_emission_coverage _ _ _ _ (by trivial)

#print axioms fragment_emission_coverage

end Goose.Lower.Validation.SourceReplacementWriterLedger
