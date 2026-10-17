import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem ownerBorrow_resultTy {le : LEnv} {before : LS} {value : ValueId} {target : Ty}
    (typed : before.vals[value]? = some (some (.data (.ref .mutable target))))
    (owner : (match target with | .grow _ | .growshrink _ => true | _ => false) = true) :
    (Op.ownerBorrow value).resultTy (tyEnv le before) = .ok (.data (.ref .mutable target)) := by
  cases target <;> simp at owner
  all_goals
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      typed, pure, Except.pure, bind, Except.bind]

theorem borrowTo_typed {le : LEnv} {before : LS} {value : ValueId} {ty : Ty}
    {actual requested : Mutability} {block : BlockId}
    (typed : before.vals[value]? = some (some (.data (.ref actual ty))))
    (permission : actual.atLeast requested = true) (live : before.cur = some block) :
    let (result, after) := borrowTo requested value le before
    after.cur = before.cur ∧ after.vals[result]? = some (some (.data (.ref requested ty))) := by
  have reader : (read : B LEnv) le before = (le, before) := rfl
  cases requested <;> cases actual
  all_goals try simp [Mutability.atLeast] at permission
  all_goals
    cases ty <;>
      simp only [borrowTo, bind_run, reader, valTy_of_recorded typed,
        Prod.fst, Prod.snd, BEq.beq, Bool.false_and, Bool.and_false,
        Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false]
  all_goals first
    | exact freezeTo_typed (le := le) (requested := .mutable) typed (by rfl) live
    | exact freezeTo_typed (le := le) (requested := .readOnly) typed (by rfl) live
    | skip
  all_goals
    split
    next selected =>
      have operation := ownerBorrow_resultTy (le := le) typed (by rfl)
      exact ⟨(emitDef_recorded live operation).2.1, (emitDef_recorded live operation).2.2.1⟩
    next => exact freezeTo_typed (le := le) (requested := .mutable) typed (by rfl) live

#print axioms borrowTo_typed

end Goose.Lower.Validation
