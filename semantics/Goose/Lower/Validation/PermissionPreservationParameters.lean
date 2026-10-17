import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.PermissionPreservationFresh
import Goose.Lower.Validation.EmittedTypingParameters

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem newBlock_initial_reference_permissions {le : LEnv} {types : List VTy}
    {result : BlockId × List ValueId} {state : LS} {value : ValueId} {target : Ty}
    (run : newBlock types le initState = (result, state))
    (member : (value, .data (.ref .mutable target)) ∈ (paramIds types #[]).zip types) :
    FreshWritableEvidence le 0 state value ∧ FreshContentsEvidence le 0 state value := by
  have generated := (GeneratedBuilderState.initState).newBlock types run
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have typed := emitted_parameter_allocated types #[] member
  let authorized : ValueId → Prop := fun candidate => candidate = value
  have bounded : ∀ candidate, authorized candidate → candidate <
      (permissionFunc le { initState with
        blocks := initState.blocks.push ⟨(paramIds types initState.vals).zip types, #[]⟩
        vals := pushParamTypes types initState.vals }).numValues := by
    intro candidate same
    subst candidate
    rw [permissionFunc_numValues generated.dense le]
    exact (Array.getElem?_eq_some_iff.mp typed).1
  have noninteger : NonIntegerParameters
      (permissionFunc le { initState with
        blocks := initState.blocks.push ⟨(paramIds types initState.vals).zip types, #[]⟩
        vals := pushParamTypes types initState.vals }) authorized := by
    intro block blockMember param parameter same intTy integer
    simp [permissionFunc, Goose.Lower.initState] at blockMember
    subst block
    have declared := emitted_parameter_allocated types #[] parameter
    change param.1 = value at same
    rw [same, typed] at declared
    have shape := Option.some.inj (Option.some.inj declared)
    rw [← shape] at integer
    cases integer
  have contents : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le { initState with
        blocks := initState.blocks.push ⟨(paramIds types initState.vals).zip types, #[]⟩
        vals := pushParamTypes types initState.vals })
      (pushParamTypes types #[]) authorized := by
    constructor
    · exact bounded
    · intro block row param parameter same
      change param.1 = value at same
      simp [same, typedPermissions, typed]
    · intro block blockMember candidate op instruction permitted
      simp [permissionFunc, Goose.Lower.initState] at blockMember
      subst block
      simp at instruction
    · intro block blockMember term instruction
      simp [permissionFunc, Goose.Lower.initState] at blockMember
      subst block
      simp at instruction
  have bindings : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le { initState with
        blocks := initState.blocks.push ⟨(paramIds types initState.vals).zip types, #[]⟩
        vals := pushParamTypes types initState.vals })
      (pushParamTypes types #[]) authorized authorized := by
    constructor
    · exact bounded
    · intro block row param parameter same
      change param.1 = value at same
      simp [same, typedPermissions, typed]
    · intro block blockMember candidate op instruction permitted
      simp [permissionFunc, Goose.Lower.initState] at blockMember
      subst block
      simp at instruction
    · intro block blockMember term instruction
      simp [permissionFunc, Goose.Lower.initState] at blockMember
      subst block
      simp at instruction
  constructor
  · exact ⟨authorized, authorized, bindings, contents, noninteger, noninteger, rfl,
      fun _ _ => Nat.zero_le _, fun _ _ => Nat.zero_le _⟩
  · exact ⟨authorized, contents, noninteger, rfl, fun _ _ => Nat.zero_le _⟩

theorem newBlock_initial_parameterTransfer {le : LEnv} {types : List VTy}
    {result : BlockId × List ValueId} {state : LS} {value : ValueId} {type : Ty}
    (profile : ArtifactProfile) (run : newBlock types le initState = (result, state))
    (member : (value, .data type) ∈ (paramIds types #[]).zip types) :
    PermissionTransfer profile (FreshWritableEvidence le 0 state)
      (FreshContentsEvidence le 0 state) value type := by
  cases type with
  | ref mu target =>
    cases mu with
    | readOnly => trivial
    | mutable =>
      have allowed := newBlock_initial_reference_permissions run member
      cases profile <;> cases target <;>
        simp only [PermissionTransfer, reduceCtorEq, ↓reduceIte] <;>
        first | exact allowed.1 | exact allowed.2 | exact allowed
  | _ => trivial

#print axioms newBlock_initial_parameterTransfer

#print axioms newBlock_initial_reference_permissions

end Goose.Lower.Validation
