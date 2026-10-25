import Goose.Lower.Validation.SummaryPreservationMutationEffects
import Goose.Lower.Validation.SummaryPreservationRefinedAppend

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_clear_effect {env : PEnv} {owner : Place} {org : OriginId}
    {roots : List RootRef} {initial before after : RState}
    (operand : rpPlace env owner initial = .ok (roots, before))
    (source : rpStmt env (.clear owner org) initial = .ok ((), after)) :
    after.eff = { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots)
      shrinks := addTargets before.eff.shrinks (rootsTargets roots) } := by
  change (do
    let rho ← rpPlace env owner
    addReads rho
    addShrinks rho) initial = .ok ((), after) at source
  obtain ⟨returned, middle, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [operand] at run
  cases run
  obtain ⟨_, readState, reading, shrinking⟩ := (st_bind_ok _ _ _ _).mp tail
  have readPair := (st_modify_ok _ _ _).mp reading
  have readEq : readState = { before with eff := { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots) } } :=
    congrArg Prod.snd readPair
  have shrinkPair := (st_modify_ok _ _ _).mp shrinking
  have shrinkEq := congrArg (fun pair => pair.2.eff) shrinkPair
  simpa only [readEq] using shrinkEq


theorem effectRefinement_read_shrink_extension (func : Func) (source : Core.Eff)
    (roots : List RootRef) :
    EffectRefinement func source { source with
      reads := addTargets source.reads (rootsTargets roots)
      shrinks := addTargets source.shrinks (rootsTargets roots) } := by
  refine ⟨?_, fun _ h => h, fun _ h => h, ?_, fun _ h => h,
    fun h => h, fun h => h, fun h => h⟩
  · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
  · exact storageTargets_mono (fun target h => addTargets_left _ _ target h)


theorem lowerStmt_clear_source_witness {env : PEnv} {owner : Place} {org : OriginId}
    {sourceRoots : List RootRef} {initialSource before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ls : LS} {le : LEnv} {block : BlockId} {address : ValueId}
    (loop : Option LoopCtx)
    (operandSource : rpPlace env owner initialSource = .ok (sourceRoots, before))
    (source : rpStmt env (.clear owner org) initialSource = .ok ((), after))
    (operandRun : lowerPlace owner le initial = (address, ls))
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) sourceRoots) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.clear owner org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.clear owner org) le initial).2 := by
  have sourceEffect := rpStmt_clear_effect operandSource source
  have extension : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) before.eff after.eff := by
    rw [sourceEffect]
    exact effectRefinement_read_shrink_extension _ _ _
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper after.eff ls :=
    fun inst member => (prior inst member).trans extension
  have delta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt upper {}
        (.eff (.clear address (some org)))) after.eff := by
    rw [sourceEffect]
    exact effectStep_clear_refines closed (effectRefinement_empty _ _) roots
  have actual := emitEffect_refined_witness (le := le) current blockBound witness priorAfter
    (effect := .clear address (some org)) trivial delta
  simpa only [lowerStmt, bind_run, operandRun] using actual

end Goose.Lower.Validation.SummaryPreservation
