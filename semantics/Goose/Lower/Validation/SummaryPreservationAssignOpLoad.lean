import Goose.Lower.Validation.SummaryPreservationAssignOpEffects
import Goose.Lower.Validation.SummaryPreservationDefFrame

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem assignOp_load_source_frame {env : PEnv} {context : ContextId}
    {op : BinOp} {place : Place} {expression : Expr} {org : OriginId}
    {initial placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {upper : Prov}
    {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {address : ValueId}
    {target : Core.Eff}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[context]? = some env.ctx)
    (implLookup : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assignOp op place expression org) initial = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt
      (lowerContextAt env.mod env.ctx env.impl) upper target ls)
    (roots : RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt upper.vals address) placeRoots)
    (addressBound : address < ls.vals.size)
    (scalar : valRefLike vt ls.vals.size = false) :
    ∃ next : Prov,
      BuilderRootWitness results vt (lowerContextAt env.mod env.ctx env.impl) next
        (emitDef (.load address) le ls).2 ∧
      BuilderEffectRefinement (lower env.mod) vt (lowerContextAt env.mod env.ctx env.impl) next target
        (emitDef (.load address) le ls).2 ∧
      rootsAt next.vals (emitDef (.load address) le ls).1 = [] ∧
      next.slots = upper.slots ∧ (emitDef (.load address) le ls).2.SymbolWF le scopeCount ∧
      (emitDef (.load address) le ls).2.cur = some block ∧
      block < (emitDef (.load address) le ls).2.blocks.size ∧
      (emitDef (.load address) le ls).1 < (emitDef (.load address) le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at source
  cases source
  have closed := lowerContextAt_parameterRoots_closed accepted contextLookup implLookup
  have loadBound := effectStep_load_refines (module := lower env.mod) (vt := vt)
    (provenance := upper) (result := ls.vals.size) closed
    (effectRefinement_empty (lowerContextAt env.mod env.ctx env.impl) before.eff) roots
  have delta := (loadBound.trans (effectRefinement_assignOp_reads (op := op))).trans wholeEffect
  obtain ⟨next, nextRoots, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, valueBound, growth⟩ := emitDef_refined_frame_growth (.load address) symbols current
      blockBound witness prior (by simpa [Op.uses] using addressBound)
      (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) delta
  refine ⟨next, nextRoots, effects, ?_, slots, nextSymbols, nextCurrent,
    nextBlockBound, valueBound, growth⟩
  rw [returned, emitDef_run _ _ current]
  simp [rootsOfDef, scalar]

end Goose.Lower.Validation.SummaryPreservation
