import Goose.Lower.Validation.SummaryPreservationLowerResize

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_resize_fill_effect {env : PEnv} {owner : Place} {size fill : Expr} {org : OriginId}
    {roots sizeRoots fillRoots : List RootRef} {initial ownerState sizeState before after : RState}
    (ownerReplay : rpPlace env owner initial = .ok (roots, ownerState))
    (sizeReplay : rpExpr env size ownerState = .ok (sizeRoots, sizeState))
    (fillReplay : rpExpr env fill sizeState = .ok (fillRoots, before))
    (source : rpStmt env (.resize owner size (some fill) org) initial = .ok ((), after)) :
    after.eff = { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots)
      writes := addTargets before.eff.writes (rootsTargets roots)
      grows := addTargets before.eff.grows (rootsTargets roots)
      shrinks := addTargets before.eff.shrinks (rootsTargets roots)
      aborts := true } := by
  simp only [rpStmt] at source
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [ownerReplay] at run
  cases run
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  rw [sizeReplay] at run
  cases run
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  rw [fillReplay] at run
  cases run
  obtain ⟨_, writeState, writing, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have writeEq : writeState = { before with eff := { before.eff with
      writes := addTargets before.eff.writes (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp writing)
  obtain ⟨_, growState, growing, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have growEq : growState = { writeState with eff := { writeState.eff with
      grows := addTargets writeState.eff.grows (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp growing)
  obtain ⟨_, readState, reading, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have readEq : readState = { growState with eff := { growState.eff with
      reads := addTargets growState.eff.reads (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp reading)
  obtain ⟨_, shrinkState, shrinking, aborting⟩ := (st_bind_ok _ _ _ _).mp tail
  have shrinkEq : shrinkState = { readState with eff := { readState.eff with
      shrinks := addTargets readState.eff.shrinks (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp shrinking)
  have abortEq : after.eff = { shrinkState.eff with aborts := true } :=
    congrArg (fun pair => pair.2.eff) ((st_modify_ok _ _ _).mp aborting)
  simpa only [shrinkEq, readEq, growEq, writeEq] using abortEq


theorem lowerStmt_resize_fill_source_witness {env : PEnv} {owner : Place} {size fill : Expr} {org : OriginId}
    {sourceRoots sizeRoots fillRoots : List RootRef} {initialSource ownerState sizeState before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ownerLS sizeLS ls : LS} {le : LEnv} {block : BlockId} {address amount value : ValueId}
    (loop : Option LoopCtx)
    (ownerReplay : rpPlace env owner initialSource = .ok (sourceRoots, ownerState))
    (sizeReplay : rpExpr env size ownerState = .ok (sizeRoots, sizeState))
    (fillReplay : rpExpr env fill sizeState = .ok (fillRoots, before))
    (source : rpStmt env (.resize owner size (some fill) org) initialSource = .ok ((), after))
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (sizeRun : lowerExpr size le ownerLS = (amount, sizeLS))
    (fillRun : lowerExpr fill le sizeLS = (value, ls))
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) sourceRoots) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.resize owner size (some fill) org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.resize owner size (some fill) org) le initial).2 := by
  have sourceEffect := rpStmt_resize_fill_effect ownerReplay sizeReplay fillReplay source
  have extension : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) before.eff after.eff := by
    rw [sourceEffect]
    refine ⟨?_, ?_, ?_, ?_, fun _ h => h, fun _ => rfl, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun target h => addTargets_left _ _ target h)
  have priorAfter : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper after.eff ls :=
    fun inst member => (prior inst member).trans extension
  have delta : EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt upper {}
        (.eff (.resize address amount (some value) (some org)))) after.eff := by
    rw [sourceEffect]
    exact effectStep_resize_refines (fill := some value) closed (effectRefinement_empty _ _) roots
  have actual := emitEffect_refined_witness (le := le) current blockBound witness priorAfter
    (effect := .resize address amount (some value) (some org)) trivial delta
  simpa only [lowerStmt, bind_run, ownerRun, sizeRun, fillRun, pure_run] using actual

end Goose.Lower.Validation.SummaryPreservation
