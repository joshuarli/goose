import Goose.Lower.Validation.EmittedMetadataEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedEffectTyped.check {le : LEnv} {state : LS} {effect : Effect}
    (typed : EmittedEffectTyped le state effect) : checkEffectTypes (tyEnv le state) effect = .ok () := by
  cases typed with
  | slotInit slotAt valueAt =>
    simp [checkEffectTypes, tyEnv, TyEnv.dataTy, TyEnv.valTy, slotAt, valueAt, pure, Except.pure, bind, Except.bind]
  | store ownerAt valueAt =>
    simp [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, valueAt,
      pure, Except.pure, bind, Except.bind]
  | append ownerAt ownerType valueAt =>
    rcases ownerType with rfl | rfl | ⟨capacity, rfl⟩
    all_goals simp [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.viewTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, valueAt,
      pure, Except.pure, bind, Except.bind]
  | popN ownerAt ownerType countAt =>
    simp [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, countAt, ownerType,
      pure, Except.pure, bind, Except.bind]
  | resize ownerAt ownerType sizeAt fillAt =>
    simp only [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, sizeAt,
      ownerType, pure, Except.pure, bind, Except.bind]
    split
    · simp [fillAt _ rfl]
    · rfl
  | clear ownerAt ownerType =>
    simp [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, ownerType,
      pure, Except.pure, bind, Except.bind]
  | replace ownerAt ownerType valueAt =>
    rcases ownerType with ⟨element, rfl⟩ | ⟨element, rfl⟩
    all_goals simp [checkEffectTypes, tyEnv, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, ownerAt, valueAt,
      pure, Except.pure, bind, Except.bind]
  | @print parts origin values =>
    induction parts with
    | nil => rfl
    | cons part rest inductionHypothesis =>
      have tail := inductionHypothesis (fun value member => values value (by simp [member]))
      cases part with
      | text text => simpa [checkEffectTypes, List.forIn_cons, pure, Except.pure, bind, Except.bind] using tail
      | val value =>
        rcases values value (by simp) with ⟨integer, row⟩ | row
        all_goals simpa [checkEffectTypes, List.forIn_cons, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
          pure, Except.pure, bind, Except.bind] using tail
  | enter scope => rfl
  | leave scope => rfl

theorem TypedValues.checkValues {state : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues state types values) (le : LEnv) :
    (do
      for (value, type) in values.zip types do
        unless (← (tyEnv le state).dataTy value) = type do
          tyErr "a returned value of another type than the result") = (.ok () : TyR Unit) := by
  induction typed with
  | nil => rfl
  | cons row tail inductionHypothesis =>
    simpa [List.zip_cons_cons, List.forIn_cons, TyEnv.dataTy, TyEnv.valTy, tyEnv, row,
      pure, Except.pure, bind, Except.bind] using inductionHypothesis

theorem TypedValues.checkReturn {state : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues state types values) (le : LEnv) (func : Func) (results : func.results = types)
    (origin : Option OriginId) : checkTermTypes func (tyEnv le state) (.ret values origin) = .ok () := by
  have count : values.length = types.length := typed.length_eq.symm
  simpa only [checkTermTypes, results, count, ite_true, ite_false, not_true_eq_false, pure, Except.pure, bind, Except.bind]
    using typed.checkValues le

theorem EmittedTermTyped.check {le : LEnv} {state : LS} {results : List Ty} {term : Term}
    (typed : EmittedTermTyped results state term) (func : Func) (same : func.results = results) :
    checkTermTypes func (tyEnv le state) term = .ok () := by
  cases typed with
  | condbr row =>
    simp [checkTermTypes, TyEnv.dataTy, TyEnv.valTy, tyEnv, row, pure, Except.pure, bind, Except.bind]
  | ret values => exact values.checkReturn le func same _
  | exit row =>
    simp [checkTermTypes, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row, pure, Except.pure, bind, Except.bind]
  | br _ _ => rfl
  | abort _ _ => rfl
  | unreachable => rfl

end Goose.Lower.Validation
