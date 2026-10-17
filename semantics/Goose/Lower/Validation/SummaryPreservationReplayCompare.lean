import Goose.Lower.Validation.SummaryPreservationReplayScalar

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem comparison {env : PEnv} {op : CmpOp} {left right : Expr}
    {initialSource middleSource before after : RState} {leftRoots rightRoots sourceRoots : List RootRef}
    {initial middle : LS} {leftValue rightValue : ValueId} {valueTy : VTy}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (leftReplay : rpExpr env left initialSource = .ok (leftRoots, middleSource))
    (rightReplay : rpExpr env right middleSource = .ok (rightRoots, before))
    (source : rpExpr env (.cmp op left right) initialSource = .ok (sourceRoots, after))
    (leftRun : lowerExpr left le initial = (leftValue, middle))
    (rightRun : lowerExpr right le middle = (rightValue, ls))
    (typeRun : valTy leftValue le ls = (valueTy, ls))
    (inputs : ls.cur.isSome = true → leftValue < ls.vals.size ∧ rightValue < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.cmp op left right) le initial).2 next ∧
      ((lowerExpr (.cmp op left right) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.cmp op left right) le initial).2
          (lowerExpr (.cmp op left right) le initial).1 sourceRoots (.data .bool)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_cmp_after_operands leftReplay rightReplay] at source
  cases source
  let emitted : Op := match valueTy with
    | .data (.int ty) => .cmp op ty leftValue rightValue
    | _ => .boolCmp op leftValue rightValue
  have whole : lowerExpr (.cmp op left right) le initial = Goose.Lower.emitDef emitted le ls := by
    simp only [lowerExpr, bind_run, leftRun, rightRun, typeRun]
    cases valueTy with
    | data ty => cases ty <;> rfl
    | view => rfl
  rw [whole]
  apply ready.emitTypedDef_live emitted [] (.data .bool)
  · intro live
    dsimp only [emitted]
    split <;> simpa [Op.uses] using inputs live
  · dsimp only [emitted]
    split <;> simp [Op.origin]
  · dsimp only [emitted]
    split <;> simp [Op.SymbolRefsValid]
  · intro _
    dsimp only [emitted]
    split <;> exact effectRefinement_empty func target
  · intro _
    dsimp only [emitted]
    split <;> intro root member <;> cases member
  · intro _ _
    dsimp only [emitted]
    split <;> rfl

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
