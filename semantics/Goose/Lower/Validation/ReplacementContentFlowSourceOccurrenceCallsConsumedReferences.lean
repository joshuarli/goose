import Goose.Lower.Validation.ReplacementContentFlowSourceConsumedReferences
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsReferenceArguments
import Goose.Lower.Validation.SummaryPreservationArgumentReplay

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem rpArgs_byRef_at {env : PEnv} {arguments : List Arg}
    {before after : RState} {sourceRoots : List (List RootRef)}
    {index : Nat} {mutability : Mutability} {place : Place} {roots : List RootRef}
    (replay : rpArgs env arguments before = .ok (sourceRoots, after))
    (argumentAt : arguments[index]? = some (.byRef mutability place))
    (rootsAt : sourceRoots[index]? = some roots) :
    ∃ first last, rpPlace env place first = .ok (roots, last) := by
  induction arguments generalizing index before sourceRoots with
  | nil => simp at argumentAt
  | cons argument rest ih =>
    obtain ⟨first, middle, remaining, headReplay, tailReplay, rfl⟩ := rpArgs_cons_contract replay
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at argumentAt rootsAt
      subst argument
      subst roots
      exact ⟨before, middle, headReplay⟩
    | succ index =>
      exact ih tailReplay (by simpa only [List.getElem?_cons_succ] using argumentAt)
        (by simpa only [List.getElem?_cons_succ] using rootsAt)

theorem call_arguments_consumed_references {typingEnv : TEnv} {env : PEnv} {callee : Core.Impl}
    {types : Array (Option VTy)} {results : List Ty} {func : Func} {upper : Prov}
    {root : DemandNode} {arguments : List Arg} {values : List ValueId} {initial final : LS}
    {start finish : Nat} {before after : RState} {sourceRoots : List (List RootRef)}
    (checked : Core.ImplementationTables typingEnv.mod callee)
    (arity : callee.params.toList.length = arguments.length)
    (source : Core.tyArgs typingEnv callee callee.params.toList arguments start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types final)
    (run : lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial = (values, final))
    (live : final.cur.isSome = true)
    (replay : rpArgs env arguments before = .ok (sourceRoots, after))
    (bounds : ∀ (index value : Nat), values[index]? = some value → value < upper.vals.size)
    (refinements : ∀ (index value : Nat), values[index]? = some value →
      ∃ roots, sourceRoots[index]? = some roots ∧ GIR.RootsRefine func (GIR.rootsAt upper.vals value) roots)
    (paths : ∀ (index : Nat) (borrowed : Mutability) (place : Place), arguments[index]? = some (.byRef borrowed place) →
      ∃ path, DemandNodeAt root path (.place place)) :
    ∀ (index value : Nat), values[index]? = some value → ∀ mutability payload,
      types[value]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper value := by
  intro index value valueAt mutability payload reference
  have nativeActual : NativeRows types
      (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 := by
    rw [run]
    exact native
  have liveActual : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.cur.isSome = true := by
    rw [run]
    exact live
  have valueActual : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).1[index]? = some value := by
    rw [run]
    exact valueAt
  obtain ⟨borrowed, place, argumentAt⟩ := call_reference_argument_is_byRef checked arity source generated
    nativeActual liveActual valueActual reference
  obtain ⟨roots, sourceAt, refined⟩ := refinements index value valueAt
  obtain ⟨first, last, placeReplay⟩ := rpArgs_byRef_at replay argumentAt sourceAt
  obtain ⟨path, atRoot⟩ := paths index borrowed place argumentAt
  exact .place value env path place first roots last rfl atRoot placeReplay
    (bounds index value valueAt) refined

#print axioms call_arguments_consumed_references

end Goose.Lower.Validation.ReplacementContentFlowSource
