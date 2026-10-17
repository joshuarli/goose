import Goose.Lower.Validation.SummaryPreservationAppendSource
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerStmt_append_source_witness {env : PEnv} {owner : Place} {view : View} {org : OriginId}
    {sourceRoots viewRoots : List RootRef} {initialSource ownerState before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ownerLS ls : LS} {le : LEnv} {block : BlockId} {address value : ValueId}
    {ownerType : Ty} {mutability : Mutability} (loop : Option LoopCtx)
    (ownerReplay : rpPlace env owner initialSource = .ok (sourceRoots, ownerState))
    (viewReplay : rpView env view ownerState = .ok (viewRoots, before))
    (source : rpStmt env (.append owner view org) initialSource = .ok ((), after))
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (viewRun : lowerView view le ownerLS = (value, ls))
    (sourceType : env.access.placeType? owner = some ownerType)
    (actualType : vt[address]? = some (some (.data (.ref mutability ownerType))))
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) sourceRoots)
    (values : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals value) viewRoots) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.append owner view org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.append owner view org) le initial).2 := by
  have sourceEffect := rpStmt_append_effect ownerReplay viewReplay
    (limitedOwner_matches_valueType sourceType actualType) source
  have extension : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) before.eff after.eff := by
    rw [sourceEffect]
    split
    · refine ⟨?_, ?_, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
      · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
      · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
      · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
      · intro found
        simp only [found, Bool.true_or]
    · refine ⟨?_, fun _ h => h, ?_, fun _ h => h, fun _ h => h,
        fun h => h, fun h => h, fun h => h⟩
      · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
      · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper after.eff ls :=
    fun inst member => (prior inst member).trans extension
  have delta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt upper {}
        (.eff (.append address value (some org)))) after.eff := by
    rw [sourceEffect]
    exact effectStep_append_refines closed (effectRefinement_empty _ _) roots values rfl
  have actual := emitEffect_refined_witness (le := le) current blockBound witness priorAfter
    (effect := .append address value (some org)) trivial delta
  simpa only [lowerStmt, bind_run, ownerRun, viewRun] using actual

end Goose.Lower.Validation.SummaryPreservation
