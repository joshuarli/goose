import Goose.Lower.Validation.PermissionInstructionControlRangeSteps

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem NewPermissionInstructions.eachLen {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result sampled : ValueId} {owner : Option ValueId}
    {regrow : Bool} (run : Goose.Lower.eachLen regrow owner sampled le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  cases regrow with
  | false =>
    simp only [Goose.Lower.eachLen,Bool.false_eq_true,ite_false,pure_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | true =>
    simp only [Goose.Lower.eachLen,ite_true] at run
    exact .counting run trivial

theorem NewPermissionInstructions.eachSampled {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result view : ValueId} {regrow : Bool}
    (run : Goose.Lower.eachSampled regrow view le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  cases regrow with
  | false =>
    simp only [Goose.Lower.eachSampled,Bool.false_eq_true,ite_false] at run
    exact .counting run trivial
  | true =>
    simp only [Goose.Lower.eachSampled,ite_true,pure_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl

theorem NewPermissionInstructions.regrowOf {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Bool} {owner : Option ValueId}
    (run : Goose.Lower.regrowOf owner le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  have stable : (Goose.Lower.regrowOf owner le before).2 = before := by
    cases owner with
    | none => rfl
    | some value =>
      simp only [Goose.Lower.regrowOf,growOwner,bind_run,valTy_run]
      cases (valTy value le before).1 with
      | data type => cases type <;> rfl
      | view => rfl
  rw [run] at stable
  change after = before at stable
  subst after
  exact .of_blocks_eq rfl

end Goose.Lower.Validation
