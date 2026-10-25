import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesControlsComplete

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem SourceLoweringAt.typePrefix {env : LEnv} {root fragment : Fragment}
    {initial before : LS} {path : List Nat}
    (source : SourceLoweringAt root env initial path fragment before) :
    TypePrefix initial before ∧ TypePrefix (fragment.finish env before) (root.finish env initial) := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj source)
    exact ⟨.refl _, .refl _⟩
  | cons index path ih =>
    simp only [SourceLoweringAt, Fragment.at?] at source
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at source
    | some child =>
      obtain ⟨next, start⟩ := child
      simp only [childAt] at source
      have childSpan := Fragment.child_span_types childAt
      have descendantSpan := ih source
      exact ⟨childSpan.1.trans descendantSpan.1, descendantSpan.2.trans childSpan.2⟩

#print axioms SourceLoweringAt.typePrefix

end Goose.Lower.Validation.SourceReplacementWriterLedger
