import Goose.Lower.Validation.SummaryPreservationLowerPopN
import Goose.Lower.Validation.SummaryPreservationMutationOwnerEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_resize_noFill_eq_popN (env : PEnv) (owner : Place) (size : Expr) (org : OriginId) :
    rpStmt env (.resize owner size none org) = rpStmt env (.popN owner size org) := by
  funext state
  rfl


theorem lowerStmt_resize_noFill_run (loop : Option LoopCtx) (owner : Place)
    (size : Expr) (org : OriginId) (le : LEnv) (ls : LS) :
    (lowerStmt loop (.resize owner size none org) le ls).2 =
      (emitEffect (.resize (lowerPlace owner le ls).1
        (lowerExpr size le (lowerPlace owner le ls).2).1 none (some org)) le
        (lowerExpr size le (lowerPlace owner le ls).2).2).2 := by
  rfl


theorem lowerStmt_resize_noFill_source_witness {env : PEnv} {owner : Place} {size : Expr} {org : OriginId}
    {sourceRoots sizeRoots : List RootRef} {initialSource ownerState before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {initial ownerLS ls : LS} {le : LEnv} {block : BlockId} {address amount : ValueId}
    (loop : Option LoopCtx)
    (ownerReplay : rpPlace env owner initialSource = .ok (sourceRoots, ownerState))
    (sizeReplay : rpExpr env size ownerState = .ok (sizeRoots, before))
    (source : rpStmt env (.resize owner size none org) initialSource = .ok ((), after))
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (sizeRun : lowerExpr size le ownerLS = (amount, ls))
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (current : ls.cur = some block) (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper before.eff ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) sourceRoots) :
    BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper
        (lowerStmt loop (.resize owner size none org) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) upper after.eff
        (lowerStmt loop (.resize owner size none org) le initial).2 := by
  rw [rpStmt_resize_noFill_eq_popN] at source
  have sourceEffect := rpStmt_popN_effect ownerReplay sizeReplay source
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
        (.eff (.resize address amount none (some org)))) after.eff := by
    rw [sourceEffect]
    exact effectStep_resize_refines (fill := none) closed (effectRefinement_empty _ _) roots
  have actual := emitEffect_refined_witness (le := le) current blockBound witness priorAfter
    (effect := .resize address amount none (some org)) trivial delta
  simpa only [lowerStmt_resize_noFill_run, ownerRun, sizeRun] using actual

end Goose.Lower.Validation.SummaryPreservation
