import Goose.Lower.Validation.SummaryPreservationScalarSource
import Goose.Lower.Validation.SummaryPreservationRefinedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_un_after_operand {op : UnOp} {operand : Expr} {origin : OriginId}
    {le : LEnv} {initial ls : LS} {value : ValueId} {ty : IntTy}
    (operandRun : lowerExpr operand le initial = (value, ls))
    (typeRun : intTyOf value le ls = (ty, ls)) :
    lowerExpr (.un op operand origin) le initial = emitDef (.un op ty value (some origin)) le ls := by
  simp only [lowerExpr, bind_run, operandRun, typeRun]


theorem lowerExpr_un_source_witness {env : PEnv} {op : UnOp} {operand : Expr}
    {origin : OriginId} {caller : Func} {upper : Prov} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {le : LEnv} {initial ls : LS} {value : ValueId} {ty : IntTy}
    {sourceInitial before after : RState} {operandRoots sourceRoots : List RootRef}
    {scopeCount : Nat} {block : BlockId}
    (operandSource : rpExpr env operand sourceInitial = .ok (operandRoots, before))
    (source : rpExpr env (.un op operand origin) sourceInitial = .ok (sourceRoots, after))
    (operandRun : lowerExpr operand le initial = (value, ls))
    (typeRun : intTyOf value le ls = (ty, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt caller upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt caller upper before.eff ls)
    (valueBound : value < ls.vals.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt caller next (lowerExpr (.un op operand origin) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt caller next after.eff
        (lowerExpr (.un op operand origin) le initial).2 ∧
      RootsRefine caller (rootsAt next.vals (lowerExpr (.un op operand origin) le initial).1)
        sourceRoots ∧ next.slots = upper.slots := by
  rw [rpExpr_un_after_operand operandSource] at source
  cases source
  rw [lowerExpr_un_after_operand operandRun typeRun]
  cases op with
  | neg =>
    have lifted : BuilderEffectRefinement (lower env.mod) vt caller upper
        { before.eff with aborts := true } ls := by
      intro inst member
      have old := prior inst member
      exact ⟨old.reads, old.writes, old.grows, old.shrinks, old.rebinds,
        fun _ => rfl, old.outputs, old.unknown⟩
    obtain ⟨next, rootsWitness, effects, roots, slots⟩ := emitDef_refined_witness
      symbols current blockBound witness lifted (op := .un .neg ty value (some origin))
      (value := (emitDef (.un .neg ty value (some origin)) le ls).1)
      (final := (emitDef (.un .neg ty value (some origin)) le ls).2)
      (by simpa [Op.uses] using valueBound)
      (effectStep_neg_refines (effectRefinement_empty caller before.eff)) rfl
    refine ⟨next, rootsWitness, effects, ?_, slots⟩
    rw [roots]
    intro root member
    cases member
  | bitnot =>
    obtain ⟨next, rootsWitness, effects, roots, slots⟩ := emitDef_refined_witness
      symbols current blockBound witness prior (op := .un .bitnot ty value (some origin))
      (value := (emitDef (.un .bitnot ty value (some origin)) le ls).1)
      (final := (emitDef (.un .bitnot ty value (some origin)) le ls).2)
      (by simpa [Op.uses] using valueBound) (effectRefinement_empty caller before.eff) rfl
    refine ⟨next, rootsWitness, effects, ?_, slots⟩
    rw [roots]
    intro root member
    cases member


theorem lowerExpr_bin_after_operands {op : BinOp} {left right : Expr} {origin : OriginId}
    {le : LEnv} {initial middle ls : LS} {leftValue rightValue : ValueId} {ty : IntTy}
    (leftRun : lowerExpr left le initial = (leftValue, middle))
    (rightRun : lowerExpr right le middle = (rightValue, ls))
    (typeRun : intTyOf leftValue le ls = (ty, ls)) :
    lowerExpr (.bin op left right origin) le initial =
      emitDef (.bin op ty leftValue rightValue (some origin)) le ls := by
  simp only [lowerExpr, bind_run, leftRun, rightRun, typeRun]


theorem lowerExpr_bin_source_witness {env : PEnv} {op : BinOp} {left right : Expr}
    {origin : OriginId} {caller : Func} {upper : Prov} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {le : LEnv} {initial middle ls : LS}
    {leftValue rightValue : ValueId} {ty : IntTy}
    {sourceInitial sourceMiddle before after : RState} {leftRoots rightRoots sourceRoots : List RootRef}
    {scopeCount : Nat} {block : BlockId}
    (leftSource : rpExpr env left sourceInitial = .ok (leftRoots, sourceMiddle))
    (rightSource : rpExpr env right sourceMiddle = .ok (rightRoots, before))
    (source : rpExpr env (.bin op left right origin) sourceInitial = .ok (sourceRoots, after))
    (leftRun : lowerExpr left le initial = (leftValue, middle))
    (rightRun : lowerExpr right le middle = (rightValue, ls))
    (typeRun : intTyOf leftValue le ls = (ty, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt caller upper ls)
    (prior : BuilderEffectRefinement (lower env.mod) vt caller upper before.eff ls)
    (leftBound : leftValue < ls.vals.size) (rightBound : rightValue < ls.vals.size) :
    ∃ next : Prov,
      BuilderRootWitness results vt caller next (lowerExpr (.bin op left right origin) le initial).2 ∧
      BuilderEffectRefinement (lower env.mod) vt caller next after.eff
        (lowerExpr (.bin op left right origin) le initial).2 ∧
      RootsRefine caller
        (rootsAt next.vals (lowerExpr (.bin op left right origin) le initial).1) sourceRoots ∧
      next.slots = upper.slots := by
  rw [rpExpr_bin_after_operands leftSource rightSource] at source
  cases source
  rw [lowerExpr_bin_after_operands leftRun rightRun typeRun]
  have lifted : BuilderEffectRefinement (lower env.mod) vt caller upper
      (if op.mayAbort then { before.eff with aborts := true } else before.eff) ls := by
    split
    · intro inst member
      have old := prior inst member
      exact ⟨old.reads, old.writes, old.grows, old.shrinks, old.rebinds,
        fun _ => rfl, old.outputs, old.unknown⟩
    · exact prior
  obtain ⟨next, rootsWitness, effects, roots, slots⟩ := emitDef_refined_witness
    symbols current blockBound witness lifted
    (op := .bin op ty leftValue rightValue (some origin))
    (value := (emitDef (.bin op ty leftValue rightValue (some origin)) le ls).1)
    (final := (emitDef (.bin op ty leftValue rightValue (some origin)) le ls).2)
    (by simpa [Op.uses] using And.intro leftBound rightBound)
    (effectStep_bin_refines (effectRefinement_empty caller before.eff)) rfl
  refine ⟨next, rootsWitness, effects, ?_, slots⟩
  rw [roots]
  intro root member
  cases member

end Goose.Lower.Validation.SummaryPreservation
