import Goose.Lower.Validation.SummaryPreservationRootBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsOfDef_call_represent {caller callee : Func} {provenance : Prov}
    {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {function : FnId} {result : ValueId} {args : List ValueId} {origin : Option OriginId}
    {sourceArgs : List (List RootRef)} {declared sourceResult : List RootRef}
    (returns : RootsRepresent callee (rootsAt results function) declared)
    (calleeRoots : ParameterRootsClosed callee)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ roots, sourceArgs[index]? = some roots ∧
        RootsRepresent caller (rootsAt provenance.vals value) roots)
    (argumentContract : ∀ index, index < args.length → callee.parameterRoots index = [.param index] ∨
      ∀ root ∈ sourceArgs[index]?.getD [], root ∈ callee.parameterRoots index)
    (sourceMapping : mapResultRoots sourceArgs [] declared = .ok sourceResult) :
    RootsRepresent caller
      (rootsOfDef results vt caller provenance result (.call function args origin)) sourceResult := by
  have mapped := (mapResultRoots_ok sourceArgs declared [] sourceResult sourceMapping).2
  intro root member concrete concreteMember
  obtain ⟨returned, returnedMember, rootMember⟩ := List.mem_flatMap.mp member
  cases returned with
  | «local» slot => simp at rootMember
  | global global =>
    have declaredGlobal := returns (.global global) returnedMember (.global global)
      (by simp [Func.expandParameterRoot])
    have rootEq : root = .global global := List.mem_singleton.mp rootMember
    subst root
    have concreteEq : concrete = .global global := List.mem_singleton.mp concreteMember
    subst concrete
    exact mapped (.global global) declaredGlobal
  | param index =>
    cases argument : args[index]? with
    | none => simp [argument] at rootMember
    | some value =>
      simp only [argument] at rootMember
      obtain ⟨sourceRoots, sourceLookup, represented⟩ := arguments index value argument
      have sourceMember := represented root rootMember concrete concreteMember
      by_cases declaredParam : RootRef.param index ∈ declared
      · obtain ⟨roots, lookup, subset⟩ := mapped (.param index) declaredParam
        rw [sourceLookup] at lookup
        cases lookup
        exact subset concrete sourceMember
      · have calleeMember : concrete ∈ callee.parameterRoots index := by
          rcases argumentContract index (List.getElem?_eq_some_iff.mp argument).1 with generic | subset
          · have declaredRoot := returns (.param index) returnedMember (.param index)
              (by simpa [Func.expandParameterRoot, generic])
            exact (declaredParam declaredRoot).elim
          · exact subset concrete (by simpa [sourceLookup] using sourceMember)
        have declaredRoot := returns (.param index) returnedMember concrete calleeMember
        rcases calleeRoots index concrete calleeMember with sameParam | ⟨global, sameGlobal⟩
        · rw [sameParam] at declaredRoot
          exact (declaredParam declaredRoot).elim
        · subst concrete
          exact mapped (.global global) declaredRoot

theorem checkArgRoots_parameterContract {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {sourceArgs : List (List RootRef)} {index : Nat}
    (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (bound : index < impl.params.size)
    (checked : checkArgRoots impl ctx sourceArgs index = .ok ()) :
    (lowerContextAt module ctx impl).parameterRoots index = [.param index] ∨
      ∀ root ∈ sourceArgs[index]?.getD [],
        root ∈ (lowerContextAt module ctx impl).parameterRoots index := by
  obtain ⟨checkedImpl, lookup, contextOk⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  let param := impl.params[index]'bound
  have parameter : impl.params[index]? = some param := Array.getElem?_eq_getElem bound
  obtain ⟨localVar, variableRow, typeContract⟩ := checkArgRoots_ok impl ctx sourceArgs index param checked parameter
  by_cases refLike : localVar.ty.isRefLike = true
  · obtain ⟨roots, annotation, contract⟩ := typeContract refLike
    have rootIdentity := lowerContextAt_parameterRoots_eq (module := module) (ctx := ctx)
      parameter annotation
    simpa only [rootIdentity] using contract
  · have absent : ctx.varRoots.find? (·.1 == param.var) = none := by
      cases annotation : ctx.varRoots.find? (·.1 == param.var) with
      | none => rfl
      | some row =>
        have key : row.1 = param.var :=
          eq_of_beq (List.find?_some (p := fun row : VarId × List RootRef => row.1 == param.var)
            (a := row) annotation)
        obtain ⟨annotatedVar, annotatedLookup, annotatedRef, _⟩ :=
          Core.Declarative.annotationRows_sound module impl ctx contextOk.annotationShape row.1 row.2
            (List.mem_of_find?_eq_some annotation)
        rw [key, variableRow] at annotatedLookup
        cases annotatedLookup
        exact (refLike annotatedRef).elim
    have missing : (lowerContextAt module ctx impl).roots.params.find? (·.1 == index) = none := by
      change (lowerContextRootInfo ctx impl).params.find? (·.1 == index) = none
      rw [lowerContextRootInfo_parameter_lookup parameter, absent]
      rfl
    left
    simp [Func.parameterRoots, missing]

end Goose.Lower.Validation.SummaryPreservation
