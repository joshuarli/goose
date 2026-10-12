import Goose.GIR.Eval

/-!
Equations of the interpreter's monad and of reading a frame, used by the proofs
about the interpreter and about the lowering.
-/

namespace Goose.GIR

open Goose.Core

instance instLawfulMonadM : LawfulMonad M := LawfulMonad.mk'
  M
  (id_map := fun x => by
    funext s
    show (match x s with | .ok a s' => Res.ok a s' | .stop e s' => .stop e s') = x s
    cases x s <;> rfl)
  (pure_bind := fun a f => rfl)
  (bind_assoc := fun x f g => by
    funext s
    show (match (match x s with | .ok a s' => f a s' | .stop e s' => .stop e s') with
      | .ok a s' => g a s' | .stop e s' => .stop e s') =
      (match x s with
        | .ok a s' => (match f a s' with | .ok b s'' => g b s'' | .stop e s'' => .stop e s'')
        | .stop e s' => .stop e s')
    cases x s <;> rfl)

theorem bind_apply (x : M α) (f : α → M β) (s : St) :
    (x >>= f) s = (match x s with | .ok a s' => f a s' | .stop e s' => .stop e s') := rfl

theorem pure_apply (a : α) (s : St) : (pure a : M α) s = .ok a s := rfl

theorem getCell_of {fr : Frame} {k : ValueId} {x : RVal} (h : fr.vals[k]? = some x) :
    getCell fr k = pure x := by
  unfold getCell; rw [h]

theorem getVal_of {fr : Frame} {k : ValueId} {v : Val} (h : fr.vals[k]? = some (.val v)) :
    getVal fr k = pure v := by
  unfold getVal; rw [getCell_of h]; rfl

theorem getView_of {fr : Frame} {k : ValueId} {vw : ViewVal} (h : fr.vals[k]? = some (.view vw)) :
    getView fr k = pure vw := by
  unfold getView; rw [getCell_of h]; rfl


end Goose.GIR
