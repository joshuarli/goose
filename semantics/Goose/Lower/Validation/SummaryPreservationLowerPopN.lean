import Goose.Lower.Validation.SummaryPreservationLowerClear

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_popN_effect {env : PEnv} {owner : Place} {count : Expr} {org : OriginId}
    {roots countRoots : List RootRef} {initial ownerState before after : RState}
    (ownerReplay : rpPlace env owner initial = .ok (roots, ownerState))
    (countReplay : rpExpr env count ownerState = .ok (countRoots, before))
    (source : rpStmt env (.popN owner count org) initial = .ok ((), after)) :
    after.eff = { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots)
      shrinks := addTargets before.eff.shrinks (rootsTargets roots)
      aborts := true } := by
  change (do
    let rho ← rpPlace env owner
    let _ ← rpExpr env count
    addReads rho
    addShrinks rho
    noteAborts) initial = .ok ((), after) at source
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [ownerReplay] at run
  cases run
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  rw [countReplay] at run
  cases run
  obtain ⟨_, readState, reading, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have readEq : readState = { before with eff := { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp reading)
  obtain ⟨_, shrinkState, shrinking, aborting⟩ := (st_bind_ok _ _ _ _).mp tail
  have shrinkEq : shrinkState = { readState with eff := { readState.eff with
      shrinks := addTargets readState.eff.shrinks (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp shrinking)
  have abortEq : after.eff = { shrinkState.eff with aborts := true } :=
    congrArg (fun pair => pair.2.eff) ((st_modify_ok _ _ _).mp aborting)
  simpa only [shrinkEq, readEq] using abortEq


theorem lowerStmt_popN_source_witness {env : PEnv} {owner : Place} {count : Expr} {org : OriginId}
    {sourceRoots countRoots : List RootRef} {initialSource ownerState before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ownerLS ls : LS} {le : LEnv} {block : BlockId} {address amount : ValueId}
    (loop : Option LoopCtx)
    (ownerReplay : rpPlace env owner initialSource = .ok (sourceRoots, ownerState))
    (countReplay : rpExpr env count ownerState = .ok (countRoots, before))
    (source : rpStmt env (.popN owner count org) initialSource = .ok ((), after))
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (countRun : lowerExpr count le ownerLS = (amount, ls))
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) sourceRoots) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.popN owner count org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.popN owner count org) le initial).2 := by
  have sourceEffect := rpStmt_popN_effect ownerReplay countReplay source
  have extension : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) before.eff after.eff := by
    rw [sourceEffect]
    have step := effectRefinement_read_shrink_extension
      (lowerContextAt env.mod env.ctx env.impl) before.eff sourceRoots
    exact ⟨step.reads, step.writes, step.grows, step.shrinks, step.rebinds,
      fun _ => rfl, step.outputs, step.unknown⟩
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper after.eff ls :=
    fun inst member => (prior inst member).trans extension
  have delta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt upper {}
        (.eff (.popN address amount (some org)))) after.eff := by
    rw [sourceEffect]
    exact effectStep_popN_refines closed (effectRefinement_empty _ _) roots
  have actual := emitEffect_refined_witness (le := le) current blockBound witness priorAfter
    (effect := .popN address amount (some org)) trivial delta
  simpa only [lowerStmt, bind_run, ownerRun, countRun] using actual

end Goose.Lower.Validation.SummaryPreservation
