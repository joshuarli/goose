import Goose.Lower.Validation.SummaryPreservationDefFrame
import Goose.Lower.Validation.SummaryPreservationLowerClear

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_pop_after_owner {env : PEnv} {owner : Place} {origin : OriginId}
    {initial before : RState} {roots : List RootRef}
    (ownerReplay : rpPlace env owner initial = .ok (roots, before)) :
    rpExpr env (.pop owner origin) initial = .ok ([], { before with eff := { before.eff with
      reads := addTargets before.eff.reads (rootsTargets roots)
      shrinks := addTargets before.eff.shrinks (rootsTargets roots)
      aborts := true } }) := by
  simp [rpExpr, ownerReplay, bind, pure, addReads, addShrinks, addRoots, noteAborts, modify,
    Except.bind, Except.pure, StateT.modifyGet, StateT.bind, StateT.pure, modifyGet,
    MonadStateOf.modifyGet] <;> rfl


theorem lowerExpr_pop_source_witness_growth {env : PEnv} {owner : Place} {origin : OriginId}
    {ownerRoots sourceRoots : List RootRef} {initialSource before after : RState}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {initial ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {address : ValueId}
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, before))
    (source : rpExpr env (.pop owner origin) initialSource = .ok (sourceRoots, after))
    (ownerRun : lowerPlace owner le initial = (address, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper before.eff ls)
    (closed : ParameterRootsClosed func)
    (roots : RootsRefine func (rootsAt upper.vals address) ownerRoots)
    (addressBound : address < ls.vals.size) (originBound : origin < le.mod.origins.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.pop owner origin) le initial).2 ∧
      BuilderEffectRefinement module vt func next after.eff (lowerExpr (.pop owner origin) le initial).2 ∧
      rootsAt next.vals (lowerExpr (.pop owner origin) le initial).1 = [] ∧
      next.slots = upper.slots ∧ (lowerExpr (.pop owner origin) le initial).2.SymbolWF le scopeCount ∧
      (lowerExpr (.pop owner origin) le initial).2.cur = some block ∧
      block < (lowerExpr (.pop owner origin) le initial).2.blocks.size ∧
      (lowerExpr (.pop owner origin) le initial).1 < (lowerExpr (.pop owner origin) le initial).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_pop_after_owner ownerReplay] at source
  cases source
  have extension : EffectRefinement func before.eff { before.eff with
      reads := addTargets before.eff.reads (rootsTargets ownerRoots)
      shrinks := addTargets before.eff.shrinks (rootsTargets ownerRoots)
      aborts := true } := by
    have step := effectRefinement_read_shrink_extension func before.eff ownerRoots
    exact ⟨step.reads, step.writes, step.grows, step.shrinks, step.rebinds,
      fun _ => rfl, step.outputs, step.unknown⟩
  have priorAfter : BuilderEffectRefinement module vt func upper
      { before.eff with
        reads := addTargets before.eff.reads (rootsTargets ownerRoots)
        shrinks := addTargets before.eff.shrinks (rootsTargets ownerRoots)
        aborts := true } ls := fun inst member => (prior inst member).trans extension
  have actual : lowerExpr (.pop owner origin) le initial = emitDef (.pop address (some origin)) le ls := by
    simp only [lowerExpr, bind_run, ownerRun]
  rw [actual]
  exact emitDef_refined_frame_growth (.pop address (some origin)) symbols current blockBound witness priorAfter
    (by simpa [Op.uses] using addressBound) (by simpa [Op.origin] using originBound)
    (by simp [Op.SymbolRefsValid]) (effectStep_pop_refines closed (effectRefinement_empty _ _) roots)

end Goose.Lower.Validation.SummaryPreservation
