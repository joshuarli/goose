import Goose.Lower.Validation.SummaryPreservationArgumentReplay
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReferenceArguments
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsTypingCheckpoints
import Goose.Core.Sound.AccessTyping

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.Core.Sound ReplacementContentFlowSource

theorem tyArgs_refSlice_local_argument {env : TEnv} {callee : Impl}
    {parameters : List Param} {arguments : List Arg} {start finish index slot : Nat}
    {parameter : Param} {parameterVar : LocalVar} {mutability : Mutability}
    (typed : tyArgs env callee parameters arguments start = .ok ((), finish))
    (arity : parameters.length = arguments.length)
    (parameterAt : parameters[index]? = some parameter)
    (mode : parameter.mode = .byRef)
    (parameterRow : callee.vars[parameter.var]? = some parameterVar)
    (reference : parameterVar.ty.isRefSlice = true)
    (argumentAt : arguments[index]? = some (.byRef mutability (.var slot))) :
    ∃ localVar, env.vars[slot]? = some localVar ∧ localVar.ty.isRefLike = true ∧
      localVar.ty.isRefSlice = false := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp argumentAt
  have split : arguments = arguments.take index ++
      .byRef mutability (.var slot) :: arguments.drop (index + 1) := by
    calc
      arguments = arguments.take index ++ arguments.drop index := (List.take_append_drop index arguments).symm
      _ = _ := by rw [List.drop_eq_getElem_cons bound, selected]
  obtain ⟨earlier, actual, later, childStart, childFinish,
    parameterSplit, parameterLength, _, currentTyped, _⟩ :=
    tyArgs_argument_checkpoint (by rw [← split]; exact arity) (by rw [← split]; exact typed)
  have actualAt : parameters[index]? = some actual := by
    rw [parameterSplit, ← List.length_take_of_le (Nat.le_of_lt bound), ← parameterLength]
    simp
  have same : actual = parameter := Option.some.inj (actualAt.symm.trans parameterAt)
  subst actual
  obtain ⟨actualMu, place, info, placeFinish, argumentEq, placeTyped, refLike, readable, _⟩ :=
    tyArgs_refSlice_head mode parameterRow reference currentTyped
  have placeEq : place = .var slot := by cases argumentEq; rfl
  subst place
  simp only [tyPlace] at placeTyped
  obtain ⟨localVar, middle, found, returned⟩ := (st_bind_ok _ _ _ _).mp placeTyped
  have declared := (varOf_ok env slot childStart (localVar, middle)).mp found
  have infoEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp returned)
  dsimp only at infoEq
  subst info
  refine ⟨localVar, declared.2.1, refLike, ?_⟩
  cases type : localVar.ty with
  | ref mu target =>
      cases target <;> try rfl
      simp [type, Ty.readable, Ty.refTarget] at readable
  | _ => rfl

theorem rpArgs_argument_replay {env : PEnv} {arguments : List Arg} {argument : Arg}
    {index : Nat} {before after : RState} {argumentRoots : List (List RootRef)} {roots : List RootRef}
    (selected : arguments[index]? = some argument)
    (replayed : rpArgs env arguments before = .ok (argumentRoots, after))
    (rootsAt : argumentRoots[index]? = some roots) :
    ∃ childBefore childAfter, SummaryPreservation.ArgumentReplay env argument childBefore roots childAfter := by
  induction arguments generalizing before argumentRoots index with
  | nil => simp at selected
  | cons first rest ih =>
      obtain ⟨headRoots, middle, tailRoots, headReplay, tailReplay, rfl⟩ :=
        SummaryPreservation.rpArgs_cons_contract replayed
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected rootsAt
          subst first
          subst headRoots
          exact ⟨before, middle, headReplay⟩
      | succ index => exact ih selected tailReplay rootsAt

#print axioms rpArgs_argument_replay

#print axioms tyArgs_refSlice_local_argument

end Goose.Lower.Validation.AdmittedSourceCalls
