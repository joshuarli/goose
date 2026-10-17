import Goose.Lower.Validation.PermissionPreservationTransport

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem PermissionRule.replace_types {module : GIR.Module} {func : Func}
    {before after : Array (Option VTy)} {writable contents : ValueId → Prop} {instruction : Inst}
    (rule : PermissionRule module func before writable contents instruction)
    (storeTypes : ∀ owner value origin, instruction = .eff (.store owner value origin) →
      before[owner]? = after[owner]?)
    (snapshotTypes : ∀ value mode owner, instruction = .def value (.snapshot mode owner) →
      before[value]? = after[value]?) :
    PermissionRule module func after writable contents instruction := by
  constructor
  · exact rule.storeBinding
  · intro owner value origin mu ty shape typed
    apply rule.storeValue owner value origin mu ty shape
    rw [storeTypes owner value origin shape]
    exact typed
  · exact rule.mutation
  · exact rule.ownerBorrow
  · exact rule.replacement
  · intro value mode owner ty shape typed
    apply rule.snapshot value mode owner ty shape
    rw [snapshotTypes value mode owner shape]
    exact typed
  · exact rule.call
  · exact rule.binding
  · exact rule.result

structure PermissionGuardTypes (types : Array (Option VTy)) (instruction : Inst) : Prop where
  store : ∀ owner value origin, instruction = .eff (.store owner value origin) →
    ∃ ty, types[owner]? = some (some ty)
  snapshot : ∀ value mode owner, instruction = .def value (.snapshot mode owner) →
    ∃ ty, types[value]? = some (some ty)

theorem PermissionGuardTypes.retained {before after : LS} {instruction : Inst}
    (known : PermissionGuardTypes before.vals instruction) (extension : TypePrefix before after) :
    PermissionGuardTypes after.vals instruction := by
  constructor
  · intro owner value origin shape
    obtain ⟨ty, typed⟩ := known.store owner value origin shape
    exact ⟨ty, extension owner ty typed⟩
  · intro value mode owner shape
    obtain ⟨ty, typed⟩ := known.snapshot value mode owner shape
    exact ⟨ty, extension value ty typed⟩

theorem PermissionRule.retained {module : GIR.Module} {func : Func} {before after : LS}
    {writable contents : ValueId → Prop} {instruction : Inst}
    (rule : PermissionRule module func before.vals writable contents instruction)
    (known : PermissionGuardTypes before.vals instruction) (extension : TypePrefix before after) :
    PermissionRule module func after.vals writable contents instruction := by
  apply rule.replace_types
  · intro owner value origin shape
    obtain ⟨ty, typed⟩ := known.store owner value origin shape
    rw [typed, extension owner ty typed]
  · intro value mode owner shape
    obtain ⟨ty, typed⟩ := known.snapshot value mode owner shape
    rw [typed, extension value ty typed]

theorem PermissionRule.replace_function {module : GIR.Module} {before after : Func}
    {types : Array (Option VTy)} {writable contents : ValueId → Prop} {instruction : Inst}
    (rule : PermissionRule module before types writable contents instruction)
    (slots : before.slots = after.slots) (results : before.results = after.results) :
    PermissionRule module after types writable contents instruction := by
  constructor
  · exact rule.storeBinding
  · exact rule.storeValue
  · exact rule.mutation
  · exact rule.ownerBorrow
  · exact rule.replacement
  · exact rule.snapshot
  · exact rule.call
  · intro slot value origin descriptor shape row
    apply rule.binding slot value origin descriptor shape
    rw [slots]
    exact row
  · intro values origin shape entry member
    apply rule.result values origin shape entry
    rw [results]
    exact member

#print axioms PermissionRule.replace_types
#print axioms PermissionRule.retained
#print axioms PermissionRule.replace_function

end Goose.Lower.Validation
