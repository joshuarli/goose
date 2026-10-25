import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessConsumed
import Goose.Lower.Validation.SummaryPreservationReplaySlices
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem occurrenceReplay_length {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {view : View}
    (source : SourceContextEnvironment typingEnv env context)
    (child : ∀ initial upper, ViewOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper) :
    ∀ initial upper, ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.len view) initial upper := by
  intro initial upper here type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  obtain ⟨info, nextCounter, childTyped, typedTail⟩ := (st_bind_ok _ _ _ _).mp typed
  have shape : type = .int .i64 := congrArg Prod.fst ((st_pure_ok _ _ _).mp typedTail)
  subst type
  obtain ⟨childRoots, childAfter, childReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have stateEq := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
  dsimp only at stateEq
  subst after
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerView view le initial
  have childNative := native.of_prefix (types_emitDef (.viewLen lowered.1) le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_emitDef (.viewLen lowered.1) le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_emitDef (.viewLen lowered.1) le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots, ledger, childSites⟩ := child initial upper
    (accessChildPresent here 0 rfl) info start nextCounter before childAfter
    childRoots childTyped childReplay ceiling ready sites targets generated childNative childMetadata childContinuation
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.length childReplay
    (show rpExpr env (.len view) before = .ok (roots, childAfter) by
      simpa only [rpExpr, childReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure] using tail)
    (initial := initial) rfl (fun live => (middleValue live).bound)
  have suffixRun : emitDef (.viewLen lowered.1) le lowered.2 = lowerExpr (.len view) le initial := rfl
  have suffixGrowth := accessRootsGrowth middleReady nextReady (adv_emitDef suffixRun).vals
  have suffix : OccurrenceLedger env (.expression (.len view)) (lowerContextAt env.mod env.ctx env.impl) vt next
      lowered.2 (lowerExpr (.len view) le initial).2 := by
    apply accessEmitDefinition suffixRun
    intro live
    refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
    · intro address member reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst address
      have oldBound : lowered.1 < middle.vals.size := by
        rw [middleReady.roots.valueSize]
        exact (middleValue live).bound
      apply accessOperandView (accessChildNode 0 rfl) childReplay (Nat.lt_of_lt_of_le oldBound suffixGrowth)
      rw [nextRoots lowered.1 oldBound]
      exact (middleValue live).refined
    · intro value address same; cases same
    · intro value callee args origin same; cases same
    · intro address member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst address
      exact False.elim (sourceView_not_reference source.tables childNative generated childTyped (rfl : lowerView view le initial = lowered) live mutability payload reference)
  refine ⟨next, nextReady, nextValue, ?_,
    ((ledger.retained suffixGrowth nextRoots).underRoot (accessChildNode 0 rfl)).trans suffix,
    childSites.emitDef suffixRun suffixGrowth nextRoots⟩
  intro old bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerView view le initial _ _ rfl).vals
  exact (nextRoots old (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots old bound)

end Goose.Lower.Validation.ReplacementContentFlowSource
