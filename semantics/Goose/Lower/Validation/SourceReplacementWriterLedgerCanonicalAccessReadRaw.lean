import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadRaw
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAccessReadLocal
import Goose.Lower.Validation.ValueBounds

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_accessNestedReadSites {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {old next : Prov}
    {env : PEnv} {siteRoot : DemandNode} {siteTargets : List BlockId} {index : VarId}
    (ready : ReplayBuilder module results types func target le scopeCount slots initial old)
    (completed : ReplayBuilder module results types func target le scopeCount slots
      (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 next)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le initial func types old)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
      (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 func types next := by
  let addressed := lowerPlace (.var index) le initial
  let loaded := lowerExpr (.read (.var index)) le initial
  have emitted : EmitsOnly NotReplacement initial (lowerExpr (.read (.deref (.read (.var index)))) le initial).2 :=
    (((emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed) trivial).trans
      (emitsOnly_emitDef (rfl : emitDef (.load addressed.1) le addressed.2 = _) trivial)).trans
      (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial))).trans
      (emitsOnly_emitDef (rfl : emitDef (.load loaded.1) le loaded.2 =
        lowerExpr (.read (.deref (.read (.var index)))) le initial) trivial)
  exact sites.of_emits emitted (types_lowerExpr (.read (.deref (.read (.var index)))) le initial _ _ rfl)
    (.of_run (generatedTargetFrame_lowerExpr none (.read (.deref (.read (.var index))))) rfl)
    (accessRootsGrowth ready completed (advB_lowerExpr (.read (.deref (.read (.var index)))) le initial _ _ rfl).vals) retained

#print axioms canonical_accessNestedReadSites

end Goose.Lower.Validation.SourceReplacementWriterLedger
