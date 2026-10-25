import Goose.Lower.Validation.BuilderTyping
import Goose.Lower.Validation.SummaryPreservationReadSource
import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem nonrefRead_record_inactive {typingEnv : TEnv} {place : Place} {type : Ty}
    {start finish : Nat} {le : LEnv}
    (source : tyExpr typingEnv (.read place) start = .ok (type, finish))
    (nonref : type.isRefLike = false) (variables : le.vars = typingEnv.vars)
    (value : ValueId) (state : LS) :
    Goose.Lower.recordReadValueRootRecipe value place le state = ((), state) := by
  cases place <;> try rfl
  rename_i variableId
  obtain ⟨info, next, typed, typeEq⟩ := tyExpr_read_place source
  simp only [tyPlace] at typed
  obtain ⟨localVar, counter, found, tail⟩ := (st_bind_ok _ _ _ _).mp typed
  have row := (varOf_ok _ _ _ _).mp found |>.2.1
  have infoEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp tail)
  dsimp only at infoEq row
  have localType : type = localVar.ty := by
    rw [typeEq, infoEq]
  have ordinary : localVar.ty.isRefSlice = false := by
    have localNonref : localVar.ty.isRefLike = false := localType ▸ nonref
    cases ty : localVar.ty <;> try rfl
    have impossible : (true : Bool) = false := by simpa only [ty, Ty.isRefLike] using localNonref
    cases impossible
  rw [recordReadValueRootRecipe_run]
  simp [variables, row, ordinary]

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem scalarRead {env : PEnv} {place : Place} {initialSource before after : RState}
    {placeRoots sourceRoots : List RootRef} {initial : LS} {address : ValueId}
    (ty : Ty) (nonref : ty.isRefLike = false)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (closed : ParameterRootsClosed func)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpExpr env (.read place) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (placeRun : lowerPlace place le initial = (address, ls))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots)
    (resultType : ls.cur.isSome = true → vt[ls.vals.size]? = some (some (.data ty)))
    (inactive : ∀ value state, Goose.Lower.recordReadValueRootRecipe value place le state = ((), state)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read place) le initial).2 next ∧
      ((lowerExpr (.read place) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read place) le initial).2
          (lowerExpr (.read place) le initial).1 sourceRoots (.data ty)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have sourceEffect := (rpExpr_read_contract placeReplay source).2
  have nodeEffect : EffectRefinement func
      { before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } target := by
    simpa only [sourceEffect] using wholeEffect
  have computedEmpty : ls.cur.isSome = true → rootsOfDef results vt func upper ls.vals.size (.load address) = [] := by
    intro live
    have scalar : valRefLike vt ls.vals.size = false := by
      simp only [valRefLike, resultType live, VTy.refLike, nonref]
    simp only [rootsOfDef, scalar, Bool.false_eq_true, ite_false]
  have whole : lowerExpr (.read place) le initial = Goose.Lower.emitDef (.load address) le ls := by
    rw [lowerExpr_read_run, placeRun]
    simp only [inactive]
  rw [whole]
  apply ready.emitTypedDef_live (.load address) sourceRoots (.data ty)
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro live
    exact (effectStep_load_refines closed (effectRefinement_empty func before.eff) (input live).2).trans nodeEffect
  · intro live root member
    rw [computedEmpty live] at member
    cases member
  · intro live _
    exact computedEmpty live

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
