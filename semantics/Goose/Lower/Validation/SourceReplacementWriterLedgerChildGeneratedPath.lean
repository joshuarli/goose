import Goose.Lower.Validation.SourceReplacementWriterLedgerChildGeneratedAll
import Goose.Lower.Validation.SourceReplacementWriterLedgerAccepted

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation

theorem Fragment.finish_generated (fragment : Fragment) (env : LEnv) (before : LS)
    (checked : GeneratedBuilderState before) (bounds : fragment.loopTargets before) :
    GeneratedBuilderState (fragment.finish env before) := by
  cases fragment with
  | expression expression => exact checked.lowerExpr expression rfl
  | place place => exact checked.lowerPlace place rfl
  | view view => exact checked.lowerView view rfl
  | bound bound => exact checked.lowerBound bound rfl
  | statement loop statement => exact checked.lowerStmt loop statement bounds rfl
  | block loop bindings want block => exact checked.lowerBlock loop bindings want block bounds rfl

theorem SourceLoweringAt.generated {env : LEnv} {root fragment : Fragment}
    {initial before : LS} {path : List Nat}
    (checked : GeneratedBuilderState initial) (bounds : root.loopTargets initial)
    (source : SourceLoweringAt root env initial path fragment before) :
    GeneratedBuilderState before ∧ fragment.loopTargets before := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj source)
    exact ⟨checked, bounds⟩
  | cons index path ih =>
    simp only [SourceLoweringAt, Fragment.at?] at source
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at source
    | some child =>
      obtain ⟨next, start⟩ := child
      simp only [childAt] at source
      have childGenerated := Fragment.child_generated checked bounds childAt
      exact ih childGenerated.1 childGenerated.2 source

theorem context_cursor_generated {module : Core.Module} {impl : Impl} {path : List Nat}
    {fragment : Fragment} {before : LS}
    (source : SourceLoweringAt (contextFragment module impl)
      (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl) path fragment before) :
    GeneratedBuilderState before ∧ fragment.loopTargets before :=
  SourceLoweringAt.generated (root := contextFragment module impl)
    (initial := contextInitial module impl) (entryReplayState_generated _ _) (by trivial) source

#print axioms Fragment.finish_generated
#print axioms SourceLoweringAt.generated
#print axioms context_cursor_generated

end Goose.Lower.Validation.SourceReplacementWriterLedger
