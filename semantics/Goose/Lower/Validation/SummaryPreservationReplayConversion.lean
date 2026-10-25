import Goose.Lower.Validation.SummaryPreservationReplayScalar

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_conv_after_operand {env : PEnv} {kind : ConvKind} {targetTy : Ty}
    {operand : Expr} {origin : OriginId} {initial before : RState} {operandRoots : List RootRef}
    (operandReplay : rpExpr env operand initial = .ok (operandRoots, before)) :
    rpExpr env (.conv kind targetTy operand origin) initial = .ok ([], { before with
      eff := match kind with | .as => { before.eff with aborts := true } | _ => before.eff }) := by
  cases kind <;> simp [rpExpr, operandReplay, bind, pure, noteAborts, modify,
    Except.bind, Except.pure, StateT.modifyGet, StateT.bind, StateT.pure,
    modifyGet, MonadStateOf.modifyGet] <;> rfl

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem conversion {env : PEnv} {kind : ConvKind} {destination : IntTy}
    {operand : Expr} {origin : OriginId} {initialSource before after : RState}
    {operandRoots sourceRoots : List RootRef} {initial : LS} {value : ValueId} {sourceTy : IntTy}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (operandReplay : rpExpr env operand initialSource = .ok (operandRoots, before))
    (source : rpExpr env (.conv kind (.int destination) operand origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (operandRun : lowerExpr operand le initial = (value, ls))
    (typeRun : intTyOf value le ls = (sourceTy, ls))
    (valueBound : ls.cur.isSome = true → value < ls.vals.size) (originBound : origin < le.mod.origins.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.conv kind (.int destination) operand origin) le initial).2 next ∧
      ((lowerExpr (.conv kind (.int destination) operand origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.conv kind (.int destination) operand origin) le initial).2
          (lowerExpr (.conv kind (.int destination) operand origin) le initial).1 sourceRoots (.data (.int destination))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_conv_after_operand operandReplay] at source
  cases source
  have whole : lowerExpr (.conv kind (.int destination) operand origin) le initial =
      Goose.Lower.emitDef (.conv kind sourceTy destination value (some origin)) le ls := by
    simp only [lowerExpr, bind_run, operandRun, typeRun]
  rw [whole]
  have delta : EffectRefinement func (func.effectStep module vt upper {}
      (.def ls.vals.size (.conv kind sourceTy destination value (some origin)))) target := by
    cases kind with
    | widen => exact effectRefinement_empty func target
    | as => exact (effectRefinement_noteAborts (effectRefinement_empty func before.eff)).trans wholeEffect
    | asUnchecked => exact effectRefinement_empty func target
  exact ready.emitTypedDef_live (.conv kind sourceTy destination value (some origin)) [] (.data (.int destination))
    (by intro live; simpa [Op.uses] using valueBound live)
    (by simpa [Op.origin] using originBound) (by simp [Op.SymbolRefsValid]) (fun _ => delta)
    (fun _ _ member => by cases member) (fun _ _ => rfl)

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
