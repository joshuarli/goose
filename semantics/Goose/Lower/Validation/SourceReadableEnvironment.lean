import Goose.Lower.Validation.SourceReadableTypes
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

structure SourceReadableEnvironment (env : Core.TEnv) : Prop where
  accepted : Core.validate env.mod = .ok ()
  variables : ∀ (index : VarId) (localVar : LocalVar), env.vars[index]? = some localVar → localVar.ty.paramOk = true

theorem SourceReadableEnvironment.tables {before after : Core.TEnv}
    (checked : SourceReadableEnvironment before)
    (moduleEq : after.mod = before.mod) (variablesEq : after.vars = before.vars) :
    SourceReadableEnvironment after := by
  constructor
  · simpa only [moduleEq] using checked.accepted
  · intro index localVar row
    rw [variablesEq] at row
    exact checked.variables index localVar row

theorem SourceReadableEnvironment.exprEnv {env : Core.TEnv}
    (checked : SourceReadableEnvironment env) : SourceReadableEnvironment (Core.exprEnv env) :=
  checked.tables rfl rfl

theorem SourceReadableEnvironment.implementation {env : Core.TEnv} {index : ImplId} {impl : Impl}
    (accepted : Core.validate env.mod = .ok ()) (lookup : env.mod.impls[index]? = some impl)
    (variablesEq : env.vars = impl.vars) : SourceReadableEnvironment env := by
  refine ⟨accepted, ?_⟩
  intro position localVar row
  rw [variablesEq] at row
  have implementation := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have one := (forAll_ok _ _).mp (checkImpl_metadata_checks implementation).2 (localVar, position)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using row))
  by_cases stored : localVar.ty.storable = true
  · exact paramOk_of_storable stored
  · have reference : localVar.ty.isRefSlice = true := by
      by_cases reference : localVar.ty.isRefSlice = true
      · exact reference
      · simp [stored, reference, chk] at one
    simp [Ty.paramOk, reference]

theorem SourceReadableEnvironment.empty {env : Core.TEnv}
    (accepted : Core.validate env.mod = .ok ()) (variables : env.vars = #[]) :
    SourceReadableEnvironment env := by
  refine ⟨accepted, ?_⟩
  intro index localVar row
  simp [variables] at row

theorem SourceReadableEnvironment.result_readable {env : Core.TEnv}
    (checked : SourceReadableEnvironment env) {index : ImplId} {impl : Impl}
    (lookup : env.mod.impls[index]? = some impl) {type : Ty} (member : type ∈ impl.results.toList) :
    type.readable = true := by
  have implementation := validate_implementation_checks checked.accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  have one := (forAll_ok _ _).mp (checkImpl_metadata_checks implementation).1 type member
  by_cases readable : type.readable = true
  · exact readable
  · simp [readable, chk] at one

theorem SourceReadableEnvironment.global_storable {env : Core.TEnv}
    (checked : SourceReadableEnvironment env) {index : GlobalId} {globalVar : Global}
    (lookup : env.mod.globals[index]? = some globalVar) : globalVar.ty.storable = true := by
  have accepted := checked.accepted
  unfold Core.validate at accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (ex_bind_ok _ _ _).mp accepted
  obtain ⟨_, globals, _⟩ := (ex_bind_ok _ _ _).mp accepted
  have bound : index < env.mod.globals.size := (Array.getElem?_eq_some_iff.mp lookup).1
  have one := (forAll_ok _ _).mp globals index (List.mem_range.mpr bound)
  rw [lookup] at one
  by_cases stored : globalVar.ty.storable = true
  · exact stored
  · simp [Core.checkGlobal, stored, chk] at one

#print axioms SourceReadableEnvironment.implementation
#print axioms SourceReadableEnvironment.global_storable

end Goose.Lower.Validation
