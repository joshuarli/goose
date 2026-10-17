import Goose.Lower.Validation.ReplacementScopedOperandsComposition

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem RhsOperandsAt.patchBrs (floor : Nat) (env : LEnv) (before : LS)
    (target : BlockId) (sources : List (BlockId × ValueId))
    (fresh : ∀ source ∈ sources, floor ≤ source.2) :
    RhsOperandsAt floor env before (Goose.Lower.patchBrs target sources) := by
  induction sources generalizing before with
  | nil => exact RhsOperandsAt.pure _ _ _ _
  | cons source rest ih =>
    simp only [Goose.Lower.patchBrs]
    apply (RhsOperandsAt.patchTerm floor env before source.1 (.br target [source.2])
      (by simpa only [Term.uses, List.mem_singleton] using
        fun value equal => equal ▸ fresh source (by simp))).bind
    exact ih _ (fun entry member => fresh entry (by simp [member]))

theorem RhsOperandsAt.patchBrs0 (floor : Nat) (env : LEnv) (before : LS)
    (target : BlockId) (sources : List BlockId) :
    RhsOperandsAt floor env before (Goose.Lower.patchBrs0 target sources) := by
  induction sources generalizing before with
  | nil => exact RhsOperandsAt.pure _ _ _ _
  | cons source rest ih =>
    simp only [Goose.Lower.patchBrs0]
    exact (RhsOperandsAt.patchTerm floor env before source (.br target []) (by simp [Term.uses])).bind
      (ih _)

theorem RhsOperandsAt.fork (floor : Nat) (env : LEnv) (before : LS)
    (value : ValueId) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.fork value) := by
  unfold Goose.Lower.fork
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro yes afterYes yesRun
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro no afterNo noRun
  have sameYes : afterYes.cur = before.cur := by
    have output := congrArg (fun pair => pair.2.cur) yesRun
    simpa only [newBlock0_run] using output.symm
  have sameNo : afterNo.cur = afterYes.cur := by
    have output := congrArg (fun pair => pair.2.cur) noRun
    simpa only [newBlock0_run] using output.symm
  apply (RhsOperandsAt.emitTerm floor env afterNo (.condbr value yes.1 [] no.1 []) ?_).bind
  · exact RhsOperandsAt.pure _ _ _ _
  · intro live source member
    have selected : source = value := by simpa [Term.uses] using member
    subst source
    exact fresh (by simpa only [sameNo, sameYes] using live)

theorem RhsOperandsAt.joinValue (floor : Nat) (env : LEnv) (before : LS)
    (yes no : Option BlockId) (yesValue noValue : ValueId)
    (yesFresh : yes.isSome = true → floor ≤ yesValue)
    (noFresh : no.isSome = true → floor ≤ noValue) :
    RhsOperandsAt floor env before (Goose.Lower.joinValue yes yesValue no noValue) := by
  unfold Goose.Lower.joinValue
  cases yes <;> cases no
  · exact (RhsOperandsAt.setCur _ _ _ _).bind (RhsOperandsAt.pure _ _ _ _)
  all_goals
    apply RhsOperandsAt.bindUnchanged (fun _ _ => valTy_run _ _ _)
    intro type
    apply (RhsOperandsAt.newBlock _ _ _ _).bind
    apply (RhsOperandsAt.patchBrs _ _ _ _ _ ?_).bind
    · exact (RhsOperandsAt.setCur _ _ _ _).bind (RhsOperandsAt.pure _ _ _ _)
    · intro pair member
      simp at member
      first
        | subst pair
        | rcases member with rfl | rfl
      all_goals first
        | exact yesFresh rfl
        | exact noFresh rfl

theorem RhsOperandsAt.joinArms (floor : Nat) (env : LEnv) (before : LS)
    (yes no : Option BlockId) :
    RhsOperandsAt floor env before (Goose.Lower.joinArms yes no) := by
  unfold Goose.Lower.joinArms
  cases yes <;> cases no
  · exact RhsOperandsAt.setCur _ _ _ _
  all_goals
    apply (RhsOperandsAt.newBlock _ _ _ _).bind
    exact (RhsOperandsAt.patchBrs0 _ _ _ _ _).bind (RhsOperandsAt.setCur _ _ _ _)

end Goose.Lower.Validation
