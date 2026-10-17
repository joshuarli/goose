import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsBorrow
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBorrow

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {initial : LS} {upper : Prov}

theorem canonical_argumentBorrowOccurrence {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}
    (mutability : Mutability) (targetType : Ty) (address : ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le initial func vt upper)
    (input : initial.cur.isSome = true → address < initial.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
        (borrowTo mutability address le initial).2 func vt next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        rootsAt next.vals (borrowTo mutability address le initial).1 = rootsAt upper.vals address) := by
  obtain ⟨next,completed,returned,retained,ledger,_,physical⟩ :=
    argumentBorrowOccurrence mutability targetType address sourceRoots ready sites.toOld input
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize,completed.roots.valueSize]
    exact (advB_borrowTo mutability address le initial _ _ rfl).vals
  refine ⟨next,completed,returned,retained,ledger,?_,physical⟩
  exact sites.of_emits (accessBorrowEmits rfl (fun _ => trivial) (fun _ => trivial))
    (types_borrowTo mutability address le initial _ _ rfl)
    (.of_run (generatedTargetFrame_borrowTo none mutability address) rfl) growth retained

#print axioms canonical_argumentBorrowOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
