import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationScalarEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem literal {env : PEnv} {before after : RState} {sourceRoots : List RootRef}
    (ty : IntTy) (literal : Int)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : rpExpr env (.lit ty literal) before = .ok (sourceRoots, after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.lit ty literal) le ls).2 next ∧
      ((lowerExpr (.lit ty literal) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.lit ty literal) le ls).2
          (lowerExpr (.lit ty literal) le ls).1 sourceRoots (.data (.int ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sameRoots : sourceRoots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  subst sourceRoots
  exact ready.emitTypedDef (.constInt ty literal) [] (.data (.int ty))
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)

theorem boolean {env : PEnv} {before after : RState} {sourceRoots : List RootRef}
    (literal : Bool)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : rpExpr env (.bool literal) before = .ok (sourceRoots, after)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.bool literal) le ls).2 next ∧
      ((lowerExpr (.bool literal) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.bool literal) le ls).2
          (lowerExpr (.bool literal) le ls).1 sourceRoots (.data .bool)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sameRoots : sourceRoots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  subst sourceRoots
  exact ready.emitTypedDef (.constBool literal) [] (.data .bool)
    (by simp [Op.uses]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)

theorem binary {env : PEnv} {op : BinOp} {left right : Expr} {origin : OriginId}
    {initialSource middleSource before after : RState} {leftRoots rightRoots sourceRoots : List RootRef}
    {initial middle : LS} {leftValue rightValue : ValueId} {ty : IntTy}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (leftReplay : rpExpr env left initialSource = .ok (leftRoots, middleSource))
    (rightReplay : rpExpr env right middleSource = .ok (rightRoots, before))
    (source : rpExpr env (.bin op left right origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (leftRun : lowerExpr left le initial = (leftValue, middle))
    (rightRun : lowerExpr right le middle = (rightValue, ls))
    (typeRun : intTyOf leftValue le ls = (ty, ls))
    (inputs : ls.cur.isSome = true → leftValue < ls.vals.size ∧ rightValue < ls.vals.size)
    (originBound : origin < le.mod.origins.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.bin op left right origin) le initial).2 next ∧
      ((lowerExpr (.bin op left right origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.bin op left right origin) le initial).2
          (lowerExpr (.bin op left right origin) le initial).1 sourceRoots (.data (.int ty))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_bin_after_operands leftReplay rightReplay] at source
  cases source
  rw [lowerExpr_bin_after_operands leftRun rightRun typeRun]
  have delta := (effectStep_bin_refines (module := module) (vt := vt) (provenance := upper)
    (result := ls.vals.size) (left := leftValue) (right := rightValue) (op := op)
    (ty := ty) (origin := some origin) (effectRefinement_empty func before.eff)).trans wholeEffect
  exact ready.emitTypedDef_live (.bin op ty leftValue rightValue (some origin)) [] (.data (.int ty))
    (by intro live; simpa [Op.uses] using inputs live)
    (by simpa [Op.origin] using originBound) (by simp [Op.SymbolRefsValid]) (fun _ => delta)
    (fun _ _ member => by cases member) (fun _ _ => rfl)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
