import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.PermissionPreservationFreshRules

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerEachSource_view_run (view : View) {le : LEnv} {before after : LS}
    {owner : Option ValueId} {value : ValueId}
    (run : lowerEachSource view le before = ((owner, value), after)) :
    lowerView view le before = (value, after) := by
  cases view with
  | of place =>
    simp only [lowerEachSource] at run
    obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
    obtain ⟨snapshot, finalState, emitted, returned⟩ := bind_eq.mp run
    obtain ⟨values, rfl⟩ := pure_eq.mp returned
    have same : snapshot = value := congrArg Prod.snd values
    subst snapshot
    simp only [lowerView, bind_run, placeRun]
    exact emitted
  | val expr =>
    simp only [lowerEachSource] at run
    obtain ⟨slice, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨snapshot, finalState, emitted, returned⟩ := bind_eq.mp run
    obtain ⟨values, rfl⟩ := pure_eq.mp returned
    have same : snapshot = value := congrArg Prod.snd values
    subst snapshot
    simp only [lowerView, bind_run, childRun]
    exact emitted

theorem lowerEachSource_generated_contents (view : View)
    {env : Core.TEnv} {element : Ty} {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, true), finish))
    {results : List Ty} {before after : LS} {owner : Option ValueId} {value : ValueId}
    (run : lowerEachSource view (lowerEnv env.mod env.vars results) before = ((owner, value), after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value :=
  lowerView_generated_contents view source (lowerEachSource_view_run view run) live generated

theorem lowerEachSource_newPermissionInstructions (view : View)
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before after : LS} {owner : Option ValueId} {value : ValueId}
    (run : lowerEachSource view le before = ((owner, value), after))
    (child : ∀ finalValue finalState, lowerView view le before = (finalValue, finalState) →
      NewPermissionInstructions module func le first before finalState) :
    NewPermissionInstructions module func le first before after :=
  child value after (lowerEachSource_view_run view run)

#print axioms lowerEachSource_view_run
#print axioms lowerEachSource_generated_contents
#print axioms lowerEachSource_newPermissionInstructions

end Goose.Lower.Validation
