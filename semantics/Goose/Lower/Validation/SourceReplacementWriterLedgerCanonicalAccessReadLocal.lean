import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationReplayAcceptedReadOrigins
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_accessLocalReadSites {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {old next : Prov}
    {env : PEnv} {siteRoot : DemandNode} {siteTargets : List BlockId} {index : VarId}
    (ready : ReplayBuilder module results types func target le scopeCount slots initial old)
    (completed : ReplayBuilder module results types func target le scopeCount slots
      (lowerExpr (.read (.var index)) le initial).2 next)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le initial func types old)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
      (lowerExpr (.read (.var index)) le initial).2 func types next := by
  let addressed := lowerPlace (.var index) le initial
  have emitted : EmitsOnly NotReplacement initial (lowerExpr (.read (.var index)) le initial).2 :=
    ((emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed) trivial).trans
      (emitsOnly_emitDef (rfl : emitDef (.load addressed.1) le addressed.2 = _) trivial)).trans
      (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial))
  exact sites.of_emits emitted (types_lowerExpr (.read (.var index)) le initial _ _ rfl)
    (.of_run (generatedTargetFrame_lowerExpr none (.read (.var index))) rfl)
    (accessRootsGrowth ready completed (advB_lowerExpr (.read (.var index)) le initial _ _ rfl).vals) retained

theorem canonical_occurrenceReplay_referenceSlicePlace {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
    {index : VarId} {localVar : LocalVar} {before after : RState} {sourceRoots : List RootRef}
    (source : SourceContextEnvironment typingEnv env context)
    (variableRow : env.impl.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (replay : rpPlace env (.deref (.read (.var index))) before = .ok (sourceRoots, after))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper)
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerPlace (.deref (.read (.var index)))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 <
          (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerPlace (.deref (.read (.var index)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots ∧
        ((env.cont index).isSome = true → ∀ root ∈ rootsAt next.vals (lowerPlace (.deref (.read (.var index)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1, root ∈ [RootRef.param index]) ∧
        rootsAt next.vals (lowerPlace (.deref (.read (.var index)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 =
            lowerValueRootCeiling env #[] (.refSliceVar index)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place (.deref (.read (.var index)))) (lowerContextAt env.mod env.ctx env.impl) vt next initial
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  obtain ⟨next, completed, value, retained, origins, physical⟩ := ready.acceptedLocalReadWithOrigins
    source.accepted source.contextRow source.implementationRow variableRow
    (show rpExpr env (.read (.var index)) before = .ok (sourceRoots, after) from replay)
    (by intro _ nonref; rw [refLike] at nonref; cases nonref) metadata
  refine ⟨next, completed, ?_, retained, ?_, canonical_accessLocalReadSites ready completed sites retained⟩
  · intro live
    obtain ⟨typed, raw⟩ := value live
    have cap : rootsAt next.vals (lowerExpr (.read (.var index))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 =
          lowerValueRootCeiling env #[] (.refSliceVar index) := by
      simpa only [reference, ite_true] using raw
    refine ⟨typed.bound, typed.refined, ?_, cap⟩
    intro observed root member
    change root ∈ rootsAt next.vals (lowerExpr (.read (.var index))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 at member
    rw [raw, if_pos reference, refSliceReadRootCeiling_observed source.accepted source.contextRow
      source.implementationRow variableRow reference observed] at member
    exact member
  · exact accessLocalReadLedger (accessChildNode 0 rfl) replay completed.roots.valueSize
      (fun live => (value live).1) origins physical

#print axioms canonical_accessLocalReadSites
#print axioms canonical_occurrenceReplay_referenceSlicePlace

end Goose.Lower.Validation.SourceReplacementWriterLedger
