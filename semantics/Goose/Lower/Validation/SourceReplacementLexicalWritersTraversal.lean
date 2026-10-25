import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansControlsComplete
import Goose.Lower.Validation.SourceReplacementLexicalWriters

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR SourceReplacementWriterLedger

theorem Fragment_at_append {root middle : Fragment} {env : LEnv} {initial before : LS}
    {front tail : List Nat}
    (atFront : root.at? env initial front = some (middle,before)) :
    root.at? env initial (front ++ tail) = middle.at? env before tail := by
  induction front generalizing root initial with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj atFront)
    rfl
  | cons index rest ih =>
    simp only [Fragment.at?,List.cons_append] at atFront ⊢
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at atFront
    | some child =>
      obtain ⟨next,start⟩ := child
      simp only [childAt] at atFront ⊢
      exact ih atFront

theorem sourceLoweringAt_descendant {root middle target : Fragment} {env : LEnv}
    {initial before current : LS} {front path : List Nat}
    (ancestor : SourceLoweringAt root env initial front middle before)
    (descendant : SourceLoweringAt root env initial path target current)
    (within : front <+: path) :
    ∃ suffix, path = front ++ suffix ∧ SourceLoweringAt middle env before suffix target current := by
  obtain ⟨suffix,same⟩ := within
  refine ⟨suffix,same.symm,?_⟩
  change middle.at? env before suffix = some (target,current)
  rw [← Fragment_at_append ancestor]
  exact same ▸ descendant

theorem sourceLoweringAt_compose {root middle target : Fragment} {env : LEnv}
    {initial before current : LS} {front tail : List Nat}
    (ancestor : SourceLoweringAt root env initial front middle before)
    (descendant : SourceLoweringAt middle env before tail target current) :
    SourceLoweringAt root env initial (front ++ tail) target current := by
  change root.at? env initial (front ++ tail) = some (target,current)
  rw [Fragment_at_append ancestor]
  exact descendant

theorem sourceLoweringAt_source {root fragment : Fragment} {env : LEnv}
    {initial before : LS} {path : List Nat}
    (source : SourceLoweringAt root env initial path fragment before) :
    DemandNodeAt root.node path fragment.node := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj source)
    exact .here _
  | cons index path ih =>
    simp only [SourceLoweringAt,Fragment.at?] at source
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at source
    | some child =>
      obtain ⟨next,start⟩ := child
      simp only [childAt] at source
      exact .child (Fragment.child_source childAt) (ih source)

theorem canonical_writer_scope_prefix {root rhs writer : Fragment} {env : LEnv}
    {initial rhsBefore writerBefore : LS} {rhsPath writerPath scopes : List Nat} {scope : Nat}
    (unique : (SourceCanonicalRootFloors.sourceNodeScopeKeys root.node).Nodup)
    (rhsAt : SourceLoweringAt root env initial rhsPath rhs rhsBefore)
    (writerAt : SourceLoweringAt root env initial writerPath writer writerBefore)
    (stackAt : lexicalScopes? root.node writerPath = some scopes)
    (active : scope ∈ ownScopeKeys writer.node ++ scopes)
    (fresh : scope ∈ SourceCanonicalRootFloors.sourceNodeScopeKeys rhs.node) : rhsPath <+: writerPath :=
  writer_scope_localization unique (sourceLoweringAt_source rhsAt) (sourceLoweringAt_source writerAt)
    stackAt active fresh

theorem canonical_writer_scope_descendant {root rhs writer : Fragment} {env : LEnv}
    {initial rhsBefore writerBefore : LS} {rhsPath writerPath scopes : List Nat} {scope : Nat}
    (unique : (SourceCanonicalRootFloors.sourceNodeScopeKeys root.node).Nodup)
    (rhsAt : SourceLoweringAt root env initial rhsPath rhs rhsBefore)
    (writerAt : SourceLoweringAt root env initial writerPath writer writerBefore)
    (stackAt : lexicalScopes? root.node writerPath = some scopes)
    (active : scope ∈ ownScopeKeys writer.node ++ scopes)
    (fresh : scope ∈ SourceCanonicalRootFloors.sourceNodeScopeKeys rhs.node) :
    ∃ suffix, writerPath = rhsPath ++ suffix ∧ SourceLoweringAt rhs env rhsBefore suffix writer writerBefore :=
  sourceLoweringAt_descendant rhsAt writerAt
    (canonical_writer_scope_prefix unique rhsAt writerAt stackAt active fresh)

private theorem sourceLoweringAt_span_induction {env : LEnv}
    (step : ∀ {parent child : Fragment} {before start : LS} {index : Nat},
      parent.child? env before index = some (child,start) →
      before.Ext start ∧ (child.finish env start).Ext (parent.finish env before))
    {root fragment : Fragment} {initial before : LS} {path : List Nat}
    (source : SourceLoweringAt root env initial path fragment before) :
    initial.Ext before ∧ (fragment.finish env before).Ext (root.finish env initial) := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj source)
    exact ⟨.refl _,.refl _⟩
  | cons index path ih =>
    simp only [SourceLoweringAt,Fragment.at?] at source
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at source
    | some child =>
      obtain ⟨next,start⟩ := child
      simp only [childAt] at source
      have childSpan := step childAt
      have descendantSpan := ih source
      exact ⟨childSpan.1.trans descendantSpan.1,descendantSpan.2.trans childSpan.2⟩

private theorem sourceLoweringAt_liveBound_induction {env : LEnv}
    (step : ∀ {parent child : Fragment} {before start : LS} {index : Nat},
      LiveBound before → parent.child? env before index = some (child,start) → LiveBound start)
    {root fragment : Fragment} {initial before : LS} {path : List Nat}
    (bounded : LiveBound initial)
    (source : SourceLoweringAt root env initial path fragment before) : LiveBound before := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj source)
    exact bounded
  | cons index path ih =>
    simp only [SourceLoweringAt,Fragment.at?] at source
    cases childAt : root.child? env initial index with
    | none => simp [childAt] at source
    | some child =>
      obtain ⟨next,start⟩ := child
      simp only [childAt] at source
      exact ih (step bounded childAt) source

theorem _root_.Goose.Lower.Validation.SourceReplacementWriterLedger.SourceLoweringAt.span
    {root fragment : Fragment} {env : LEnv} {initial before : LS} {path : List Nat}
    (source : SourceLoweringAt root env initial path fragment before) :
    initial.Ext before ∧ (fragment.finish env before).Ext (root.finish env initial) :=
  sourceLoweringAt_span_induction (fun row => Fragment.child_span row) source

theorem _root_.Goose.Lower.Validation.SourceReplacementWriterLedger.SourceLoweringAt.liveBound
    {root fragment : Fragment} {env : LEnv} {initial before : LS} {path : List Nat}
    (source : SourceLoweringAt root env initial path fragment before)
    (bounded : LiveBound initial) : LiveBound before :=
  sourceLoweringAt_liveBound_induction
    (fun bounded row => Fragment.child_liveBound bounded row) bounded source

#print axioms SourceLoweringAt.span
#print axioms SourceLoweringAt.liveBound
#print axioms Fragment_at_append
#print axioms sourceLoweringAt_descendant
#print axioms sourceLoweringAt_compose
#print axioms sourceLoweringAt_source
#print axioms canonical_writer_scope_prefix
#print axioms canonical_writer_scope_descendant

end Goose.Lower.Validation.SourceReplacementLexicalWriters
