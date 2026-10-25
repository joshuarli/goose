import Goose.Lower.Validation.SummaryPreservationAssignSource
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_assign_nonref_source_witness {env : PEnv} {context : ContextId}
    {place : Place} {expression : Expr} {org : OriginId} {placeRoots storedRoots : List RootRef}
    {initialSource placeState before after : RState} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {upper : Prov} {initial placeLS ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {address value : ValueId} (loop : Option LoopCtx)
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (storedRoots, before))
    (source : rpStmt env (.assign place expression org) initialSource = .ok ((), after))
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (valueRun : lowerExpr expression le placeLS = (value, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt upper.vals address) placeRoots)
    (emptyValue : rootsAt upper.vals value = [])
    (owner : (ownerTy vt address).any Ty.isRefLike = false)
    (addressBound : address < ls.vals.size) (valueBound : value < ls.vals.size)
    (originBound : org < le.mod.origins.size) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.assign place expression org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.assign place expression org) le initial).2 ∧
      (lowerStmt loop (.assign place expression org) le initial).2.SymbolWF le scopeCount ∧
      (lowerStmt loop (.assign place expression org) le initial).2.cur = some block := by
  have sourceEffect := (rpStmt_assign_contract placeReplay valueReplay source).2
  have extension : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) before.eff after.eff := by
    rw [sourceEffect]
    refine ⟨fun _ h => h, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
    · intro target member
      exact addTargets_left _ _ target member
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper after.eff ls :=
    fun inst member => (prior inst member).trans extension
  have delta := effectStep_store_nonref_refines (vt := vt) (provenance := upper)
    (value := value) (origin := org) (source := before.eff) accepted contextLookup implLookup roots owner
  have finalDelta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt upper {}
        (.eff (.store address value (some org)))) after.eff := by
    rw [sourceEffect]
    exact ⟨delta.reads, delta.writes, delta.grows, delta.shrinks,
      fun target member => addTargets_left _ _ target (delta.rebinds target member),
      delta.aborts, delta.outputs, delta.unknown⟩
  have stored : InstructionRootsClosed results vt
      { lowerContextAt env.mod env.ctx env.impl with blocks := finishBlocks ls.blocks } upper
      (.eff (.store address value (some org))) := by
    intro slot slotMember root member
    rw [emptyValue] at member
    cases member
  have completed := emitEffect_refined_witness (le := le) current blockBound witness priorAfter stored finalDelta
  have completedSymbols : (emitEffect (.store address value (some org)) le ls).2.SymbolWF le scopeCount := by
    rw [emitEffect_run _ _ current]
    apply LS.SymbolWF.emitEffect symbols blockBound
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro addressBound valueBound
    · simpa [Effect.origin] using originBound
    · simp [Effect.SymbolRefsValid]
  have whole : lowerStmt loop (.assign place expression org) le initial =
      emitEffect (.store address value (some org)) le ls := by
    simp only [lowerStmt, bind_run, placeRun, valueRun]
  rw [whole]
  refine ⟨completed.1, completed.2, completedSymbols, ?_⟩
  rw [emitEffect_run _ _ current]
  exact current

end Goose.Lower.Validation.SummaryPreservation
