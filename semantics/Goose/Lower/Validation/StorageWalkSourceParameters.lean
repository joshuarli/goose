import Goose.Lower.Validation.StorageWalkSourceFacts
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_impl_visible {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) (stack : List ScopeId) :
    StorageWalkVisible (implEnv module impl) (impl.body.scope :: stack) := by
  have source := checkImpl_ok module impl checked
  intro index localVar member row
  have bound : index < impl.params.size := List.mem_range.mp member
  have parameterAt : impl.params[index]? = some impl.params[index] := by simp [bound]
  obtain ⟨variableEq, actual, actualAt, scope, parameterType⟩ := source.params index impl.params[index] parameterAt
  have localAt : impl.vars[index]? = some localVar := row
  have same : actual = localVar := Option.some.inj (actualAt.symm.trans localAt)
  subst actual
  rw [scope, source.bodyScope]
  exact List.mem_cons_self

theorem storageWalk_impl_pre_scopes {module : Core.Module} {impl : Core.Impl}
    (checked : Core.checkImpl module impl = .ok ()) (values : List ValueId) (stack : List ScopeId) :
    ∀ entry ∈ (impl.params.toList.zip values).map (fun (pair : Param × ValueId) =>
      (pair.1.var, pair.2, (impl.vars[pair.1.var]?.map (fun (localVar : LocalVar) => localVar.org)).getD 0)),
      ∀ descriptor, (lowerEnv module impl.vars impl.results.toList).slots[entry.1]? = some descriptor →
        descriptor.scope ∈ impl.body.scope :: stack := by
  have source := checkImpl_ok module impl checked
  intro entry member descriptor row
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  have parameterMember := (List.of_mem_zip paired).1
  obtain ⟨index, parameterAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp parameterMember)
  obtain ⟨variableEq, localVar, localAt, scope, parameterType⟩ := source.params index param parameterAt
  have localRow : impl.vars[param.var]? = some localVar := by simpa only [variableEq] using localAt
  have descriptorEq : (⟨localVar.ty, localVar.kind, localVar.scope, param.var⟩ : Slot) = descriptor := by
    simpa [lowerEnv, Array.getElem?_mapIdx, localRow] using row
  rw [← descriptorEq]
  change localVar.scope ∈ impl.body.scope :: stack
  rw [scope, source.bodyScope]
  exact List.mem_cons_self

#print axioms storageWalk_impl_visible
#print axioms storageWalk_impl_pre_scopes

end Goose.Lower.Validation
