import Goose.Lower.Validation.AdmittedSourceCallsContentRows
import Goose.Lower.Validation.AdmittedSourceInstructionsObserved

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpArgs_length {env : PEnv} {arguments : List Arg} {before after : RState}
    {roots : List (List RootRef)}
    (checked : rpArgs env arguments before = .ok (roots, after)) :
    roots.length = arguments.length := by
  induction arguments generalizing before after roots with
  | nil =>
    have pair := (st_pure_ok _ _ _).mp checked
    have same := congrArg Prod.fst pair
    simpa using congrArg List.length same
  | cons argument rest ih =>
    cases argument with
    | byVal expression =>
      simp only [rpArgs] at checked
      obtain ⟨head, middle, replay, tail⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨tailRoots, finish, restReplay, returned⟩ := (st_bind_ok _ _ _ _).mp tail
      have pair := (st_pure_ok _ _ _).mp returned
      have same := congrArg Prod.fst pair
      dsimp only at same
      rw [same]
      simpa using congrArg Nat.succ (ih restReplay)
    | byRef mutability place =>
      simp only [rpArgs] at checked
      obtain ⟨head, middle, replay, tail⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨tailRoots, finish, restReplay, returned⟩ := (st_bind_ok _ _ _ _).mp tail
      have pair := (st_pure_ok _ _ _).mp returned
      have same := congrArg Prod.fst pair
      dsimp only at same
      rw [same]
      simpa using congrArg Nat.succ (ih restReplay)

theorem contentShape_reference {module : Core.Module} {impl : Impl} {context : Context}
    {variableId : VarId} {ceiling : List RootRef}
    (checked : checkContentShape module impl context = .ok ())
    (contents : (context.contentRoots.find? (·.1 == variableId)).map (·.2) = some ceiling) :
    ((impl.vars[variableId]?).any (·.ty.isRefSlice)) = true := by
  cases found : context.contentRoots.find? (·.1 == variableId) with
  | none => simp [found] at contents
  | some entry =>
    obtain ⟨index, roots⟩ := entry
    have indexEq : index = variableId := by simpa using List.find?_some found
    subst index
    have row := (forAll_ok _ _).1 checked _ (List.mem_of_find?_eq_some found)
    dsimp only at row
    inv at row
    obtain ⟨_, row⟩ := row
    cases variableFound : impl.vars[variableId]? with
    | none => simp only [variableFound] at row; inv at row
    | some localVar =>
      simp only [variableFound] at row
      inv at row
      obtain ⟨reference, _, _⟩ := row
      simpa [variableFound] using reference

theorem accepted_content_reference
    {module : Core.Module} {contextId : ContextId} {context : Context} {impl : Impl}
    {env : PEnv} {variableId : VarId} {ceiling : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextFound : module.contexts[contextId]? = some context)
    (implementationFound : module.impls[context.impl]? = some impl)
    (access : env.access = ⟨module, impl, context⟩)
    (contents : env.cont variableId = some ceiling) :
    env.isRefSliceVar variableId = true := by
  obtain ⟨foundImpl, found, checked⟩ := (validate_modOk module accepted).ctx contextId context contextFound
  rw [implementationFound] at found
  cases found
  have contextEq : env.ctx = context := congrArg AccessEnv.ctx access
  have implEq : env.impl = impl := congrArg AccessEnv.impl access
  have annotation : (context.contentRoots.find? (·.1 == variableId)).map (·.2) = some ceiling := by
    simpa only [PEnv.cont, contextEq] using contents
  have reference := contentShape_reference checked.contentShape annotation
  cases variableFound : impl.vars[variableId]? <;>
    simpa [PEnv.isRefSliceVar, implEq, variableFound] using reference

end Goose.Lower.Validation.AdmittedSourceCalls
