import Goose.Lower.Validation.Summary

namespace Goose.Lower.Validation

open Goose.Core

theorem checkResultV_single {env : PEnv} {roots : List RootRef}
    (checked : checkResultV env roots = .ok ()) :
    ∃ declared, env.ctx.resultRoots = [declared] := by
  unfold checkResultV at checked
  obtain ⟨_, _, shape⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  cases results : env.ctx.resultRoots with
  | nil => simp [results, reject] at shape
  | cons declared rest =>
    cases rest with
    | nil => exact ⟨declared, rfl⟩
    | cons next rest => simp [results, reject] at shape

theorem checkResultShape_size {module : Module} {impl : Impl} {ctx : Context}
    (checked : checkResultShape module impl ctx = .ok ()) :
    ctx.resultRoots.length = impl.results.size := by
  by_cases shape : ctx.resultRoots.length = impl.results.size
  · exact shape
  · simp [checkResultShape, shape, reject, bind, Except.bind] at checked

theorem validate_tailResult_size {module : Module} {index : ImplId} {impl : Impl}
    (accepted : validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (value : impl.body.value.isSome = true) : impl.results.size = 1 := by
  have bound : index < module.impls.size := (Array.getElem?_eq_some_iff.mp lookup).1
  obtain ⟨ctx, member, identity⟩ :=
    checkImplementationContexts_member (validate_implementationContexts accepted) bound
  obtain ⟨ctxIndex, ctxLookup⟩ :=
    Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨source, sourceLookup, context⟩ :=
    (Core.Sound.validate_modOk module accepted).ctx ctxIndex ctx ctxLookup
  rw [identity, lookup] at sourceLookup
  cases sourceLookup
  obtain ⟨roots, _, _, _, result, _⟩ := context.body
  obtain ⟨declared, single⟩ := checkResultV_single (result value)
  have size := checkResultShape_size context.resultShape
  rw [single] at size
  simpa using size.symm

theorem validate_zeroResults_no_tail {module : Module} {index : ImplId} {impl : Impl}
    (accepted : validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (empty : impl.results.size = 0) : impl.body.value = none := by
  cases value : impl.body.value with
  | none => rfl
  | some expr =>
    have one := validate_tailResult_size accepted lookup (by simp [value])
    omega

theorem validate_results_size {module : Module} {index : ImplId} {impl : Impl}
    (accepted : validate module = .ok ()) (lookup : module.impls[index]? = some impl) :
    impl.results.size ≤ 1 := by
  obtain ⟨_, _, _, shape⟩ := (Core.Sound.validate_modOk module accepted).impl index impl lookup |>.body
  rcases shape with ⟨empty, _⟩ | ⟨ty, single, _, _⟩
  · have length := congrArg List.length empty
    simp only [Array.length_toList, List.length_nil, List.length_singleton] at length
    omega
  · have length := congrArg List.length single
    simp only [Array.length_toList, List.length_nil, List.length_singleton] at length
    omega

theorem validate_finishReturn_arity {module : Module} {index : ImplId} {impl : Impl}
    (accepted : validate module = .ok ()) (lookup : module.impls[index]? = some impl)
    (returning : (!impl.results.isEmpty && impl.body.value.isNone &&
      impl.body.diverges module.noReturn) = false) (value : GIR.ValueId) :
    (if impl.body.value.isSome then [value] else []).length = impl.results.size := by
  cases bodyValue : impl.body.value with
  | some expr =>
    have one := validate_tailResult_size accepted lookup (by simp [bodyValue])
    simp [bodyValue, one]
  | none =>
    obtain ⟨_, _, _, shape⟩ := (Core.Sound.validate_modOk module accepted).impl index impl lookup |>.body
    rcases shape with ⟨empty, _⟩ | ⟨ty, single, _, diverges⟩
    · have zero := congrArg List.length empty
      simp only [Array.length_toList, List.length_nil] at zero
      simp [bodyValue, zero]
    · have nonempty : impl.results.isEmpty = false := by
        have one := congrArg List.length single
        simp only [Array.length_toList, List.length_singleton] at one
        simp [Array.isEmpty, one]
      have divergence := diverges (by simp [bodyValue])
      simp [nonempty, bodyValue, divergence] at returning

end Goose.Lower.Validation
