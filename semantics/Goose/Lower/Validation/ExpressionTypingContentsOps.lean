import Goose.Lower.Validation.ExpressionTypingMutableElemOps
import Goose.Lower.Validation.ExpressionTypingContentsEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerView_of_writable_typed_of_place {env : Core.TEnv} {place : Place} {info : PlaceInfo}
    {element : Ty} {start placeFinish finish : Nat}
    (placeSource : Core.tyPlace env place start = .ok (info, placeFinish))
    (source : Core.tyView env (.of place) start = .ok ((element, true), finish))
    {results : List Ty} {before mid : LS} {value : ValueId} {mu : Mutability} {block : BlockId}
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, mid))
    (placeTyped : mid.vals[value]? = some (some (.data (.ref mu info.ty))))
    (evidence : ContentsEvidence (lowerEnv env.mod env.vars results) mid value)
    (live : mid.cur = some block) :
    let (result, after) := lowerView (.of place) (lowerEnv env.mod env.vars results) before
    after.cur = mid.cur ∧ after.vals[result]? = some (some (.view .mutable element)) := by
  simp only [Core.tyView] at source
  obtain ⟨sourceInfo, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  rw [placeSource] at child
  cases Except.ok.inj child
  have operation :
      (Op.snapshot ((fun candidate : Place => match candidate with | .var _ | .global _ => .owner | _ => .borrowed) place) value).resultTy
        (tyEnv (lowerEnv env.mod env.vars results) mid) = .ok (.view .mutable element) := by
    cases ownerTy : info.ty <;> simp only [ownerTy] at source
    all_goals try exact (rej_ok _ _ _ _).mp source |>.elim
    all_goals
      have pair := (st_pure_ok _ _ _).mp source
      have elementShape := congrArg (fun pair => pair.1.1) pair
      dsimp only at elementShape
      rw [elementShape]
      have writable := evidence.contentsWritable
      have refCheck : (tyEnv (lowerEnv env.mod env.vars results) mid).refTy value = .ok (mu, info.ty) := by
        simp [TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, placeTyped, pure, Except.pure, bind, Except.bind]
      simp only [Op.resultTy, refCheck, ownerTy, arrayElem?, writable,
        Option.getD_some, ite_true, pure, Except.pure, bind, Except.bind]
  simp only [lowerView, bind_run, placeRun]
  have emitted := emitDef_recorded live operation
  exact ⟨emitted.2.1, emitted.2.2.1⟩

end Goose.Lower.Validation
