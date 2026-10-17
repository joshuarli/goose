import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound

theorem tyArgs_refSlice_head {env : TEnv} {callee : Core.Impl} {parameter : Param}
    {parameters : List Param} {argument : Arg} {arguments : List Arg} {start finish : Nat}
    {parameterVar : LocalVar}
    (mode : parameter.mode = .byRef)
    (parameterRow : callee.vars[parameter.var]? = some parameterVar)
    (reference : parameterVar.ty.isRefSlice = true)
    (typed : Core.tyArgs env callee (parameter :: parameters) (argument :: arguments) start = .ok ((), finish)) :
    ∃ mutability place info childFinish,
      argument = .byRef mutability place ∧
      Core.tyPlace env place start = .ok (info, childFinish) ∧
      info.ty.isRefLike = true ∧ info.ty.readable = true ∧
      (mutability = .mutable → info.referenceWritable env.mod.profile = true) := by
  cases argument with
  | byVal expression =>
    simp only [Core.tyArgs, Core.argMode, mode] at typed
    obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simp [rej_ok] at rejected
  | byRef mutability place =>
    obtain ⟨actual, info, childFinish, restStart, row, checked, writable, passable, _⟩ :=
      tyArgs_byRef_head typed
    have same : actual = parameterVar := Option.some.inj (row.symm.trans parameterRow)
    subst actual
    have payload : info.ty.isRefLike = true ∧ info.ty.readable = true := by
      cases type : parameterVar.ty with
      | ref parameterMu target =>
        cases target with
        | slice sliceMu element =>
          rw [type] at passable
          have samePayload : info.ty = .slice sliceMu element := by
            simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
            exact passable.1
          have elementFlat : element.flat = true := by simpa [type, Ty.isRefSlice] using reference
          simp [samePayload, Ty.isRefLike, Ty.readable, elementFlat]
        | _ => simp [type, Ty.isRefSlice] at reference
      | _ => simp [type, Ty.isRefSlice] at reference
    exact ⟨mutability, place, info, childFinish, rfl, checked, payload.1, payload.2, writable⟩

#print axioms tyArgs_refSlice_head

end Goose.Lower.Validation.ReplacementContentFlowSource
