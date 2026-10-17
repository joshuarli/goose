import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationReplayAcceptedReadOrigins
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accessLocalReadLedger {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {initial : LS}
    {index : VarId} {path : List Nat} {before after : RState} {sourceRoots : List RootRef} {type : VTy}
    (node : DemandNodeAt root path (.expression (.read (.var index))))
    (source : rpExpr env (.read (.var index)) before = .ok (sourceRoots, after))
    (size : upper.vals.size = (lowerExpr (.read (.var index)) le initial).2.vals.size)
    (returned : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      ReplayValue func upper (lowerExpr (.read (.var index)) le initial).2
        (lowerExpr (.read (.var index)) le initial).1 sourceRoots type)
    (origins : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      ∃ placeRoots placeAfter, rpPlace env (.var index) before = .ok (placeRoots, placeAfter) ∧
        (lowerPlace (.var index) le initial).1 < (lowerExpr (.read (.var index)) le initial).2.vals.size ∧
        GIR.RootsRefine func (rootsAt upper.vals (lowerPlace (.var index) le initial).1) placeRoots)
    (physical : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true →
      rootsAt upper.vals (lowerPlace (.var index) le initial).1 = [.local index]) :
    OccurrenceLedger env root func types upper initial (lowerExpr (.read (.var index)) le initial).2 := by
  let addressed := lowerPlace (.var index) le initial
  have first : OccurrenceLedger env root func types upper initial addressed.2 :=
    emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed)
      (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
  let loaded := emitDef (.load addressed.1) le addressed.2
  have run : emitDef (.load addressed.1) le addressed.2 =
      ((lowerExpr (.read (.var index)) le initial).1, loaded.2) := by
    rw [ReplayBuilder.readValue_eq]
  refine first.trans ((accessEmitDefinition run ?_).trans
    (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial)))
  intro active
  have live : (lowerExpr (.read (.var index)) le initial).2.cur.isSome = true := by
    rw [ReplayBuilder.readCurrent_eq]
    exact (congrArg Option.isSome (accessEmitCurrent run)).trans active
  obtain ⟨placeRoots, placeAfter, placeReplay, bound, refined⟩ := origins live
  have addressBound : addressed.1 < upper.vals.size := by simpa only [size] using bound
  have resultBound : (lowerExpr (.read (.var index)) le initial).1 < upper.vals.size := by
    rw [size]
    exact (returned live).bound
  refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
  · intro address member reference
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst address
    exact accessOperandPlace (node.snoc 0 rfl) placeReplay addressBound refined
  · intro value address same reference
    cases same
    exact ⟨env, path, .var index, before, placeRoots, placeAfter, sourceRoots, after,
      rfl, node, placeReplay, source, addressBound, resultBound, refined, (returned live).refined, .local index rfl (physical live)⟩
  · intro value callee args origin same; cases same
  · intro value member mutability payload typed
    simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
    subst value
    exact .place _ env _ _ _ _ _ rfl (node.snoc 0 rfl) placeReplay addressBound refined

theorem accessLocalReadSites {module : GIR.Module} {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {old next : Prov}
    {env : PEnv} {siteRoot : DemandNode} {siteTargets : List BlockId} {index : VarId}
    (ready : ReplayBuilder module results types func target le scopeCount slots initial old)
    (completed : ReplayBuilder module results types func target le scopeCount slots
      (lowerExpr (.read (.var index)) le initial).2 next)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le initial func types old)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    OccurrenceSitesBuilder env siteRoot siteTargets le
      (lowerExpr (.read (.var index)) le initial).2 func types next := by
  let addressed := lowerPlace (.var index) le initial
  have emitted : EmitsOnly NotReplacement initial (lowerExpr (.read (.var index)) le initial).2 :=
    ((emitsOnly_emitDef (rfl : emitDef (.slotAddr index) le initial = addressed) trivial).trans
      (emitsOnly_emitDef (rfl : emitDef (.load addressed.1) le addressed.2 = _) trivial)).trans
      (.of_blocks (ReplayBuilder.readBlocks_eq (.var index) le initial))
  exact sites.of_emits emitted (types_lowerExpr (.read (.var index)) le initial _ _ rfl)
    (.of_run (generatedTargetFrame_lowerExpr none (.read (.var index))) rfl)
    (accessRootsGrowth ready completed (advB_lowerExpr (.read (.var index)) le initial _ _ rfl).vals) retained

theorem occurrenceReplay_referenceSlicePlace {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
    {index : VarId} {localVar : LocalVar} {before after : RState} {sourceRoots : List RootRef}
    (source : SourceContextEnvironment typingEnv env context)
    (variableRow : env.impl.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (replay : rpPlace env (.deref (.read (.var index))) before = .ok (sourceRoots, after))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets
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
      OccurrenceSitesBuilder env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  obtain ⟨next, completed, value, retained, origins, physical⟩ := ready.acceptedLocalReadWithOrigins
    source.accepted source.contextRow source.implementationRow variableRow
    (show rpExpr env (.read (.var index)) before = .ok (sourceRoots, after) from replay)
    (by intro _ nonref; rw [refLike] at nonref; cases nonref) metadata
  refine ⟨next, completed, ?_, retained, ?_, accessLocalReadSites ready completed sites retained⟩
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

#print axioms accessLocalReadLedger
#print axioms accessLocalReadSites
#print axioms occurrenceReplay_referenceSlicePlace

end Goose.Lower.Validation.ReplacementContentFlowSource
