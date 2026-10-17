import Goose.Lower.Validation.SummaryPreservationReplayScalar

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem unary {env : PEnv} {op : UnOp} {operand : Expr} {origin : OriginId}
    {initialSource before after : RState} {operandRoots sourceRoots : List RootRef}
    {initial : LS} {value : ValueId} {ty : IntTy}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (operandReplay : rpExpr env operand initialSource = .ok (operandRoots, before))
    (source : rpExpr env (.un op operand origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (operandRun : lowerExpr operand le initial = (value, ls))
    (typeRun : intTyOf value le ls = (ty, ls))
    (valueBound : value < ls.vals.size) (originBound : origin < le.mod.origins.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.un op operand origin) le initial).2 next ∧
      ((lowerExpr (.un op operand origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.un op operand origin) le initial).2
          (lowerExpr (.un op operand origin) le initial).1 sourceRoots (.data (.int ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_un_after_operand operandReplay] at source
  cases source
  rw [lowerExpr_un_after_operand operandRun typeRun]
  have delta : EffectRefinement func
      (func.effectStep module vt upper {} (.def ls.vals.size (.un op ty value (some origin)))) target := by
    cases op with
    | neg => exact (effectStep_neg_refines (effectRefinement_empty func before.eff)).trans wholeEffect
    | bitnot => exact effectRefinement_empty func target
  exact ready.emitTypedDef (.un op ty value (some origin)) [] (.data (.int ty))
    (by simpa [Op.uses] using valueBound)
    (by simpa [Op.origin] using originBound) (by simp [Op.SymbolRefsValid]) delta
    (fun _ member => by cases member) (fun _ => rfl)

theorem logicalNot {env : PEnv} {operand : Expr} {initialSource before after : RState}
    {operandRoots sourceRoots : List RootRef} {initial : LS} {value : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (operandReplay : rpExpr env operand initialSource = .ok (operandRoots, before))
    (source : rpExpr env (.not operand) initialSource = .ok (sourceRoots, after))
    (operandRun : lowerExpr operand le initial = (value, ls))
    (valueBound : value < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.not operand) le initial).2 next ∧
      ((lowerExpr (.not operand) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.not operand) le initial).2
          (lowerExpr (.not operand) le initial).1 sourceRoots (.data .bool)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have replay : rpExpr env (.not operand) initialSource = .ok ([], before) := by
    simp [rpExpr, operandReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure]
  rw [replay] at source
  cases source
  have whole : lowerExpr (.not operand) le initial = Goose.Lower.emitDef (.boolNot value) le ls := by
    simp only [lowerExpr, bind_run, operandRun]
  rw [whole]
  exact ready.emitTypedDef (.boolNot value) [] (.data .bool)
    (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
