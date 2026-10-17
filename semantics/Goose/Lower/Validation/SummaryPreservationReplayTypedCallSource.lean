import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_call_arguments {env : TEnv} {calleeId : ContextId} {ctx : Context}
    {callee : Impl} {arguments : List Arg} {origin : OriginId} {start finish : Nat} {type : Ty}
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (source : tyExpr env (.call calleeId arguments origin) start = .ok (type, finish)) :
    arguments.length = callee.params.size ∧ ∃ middle,
      tyArgs env callee callee.params.toList arguments start = .ok ((), middle) ∧
      callResultTy callee middle = .ok (type, finish) := by
  simp only [tyExpr, contextLookup, implLookup] at source
  inv at source
  obtain ⟨_origin, arity, middle, argumentsTyped, next, initialization, resultShape, resultCounter⟩ := source
  have same := checkInitCall_state env callee middle ((), next) initialization
  exact ⟨arity.symm, middle, argumentsTyped,
    (callResultTy_ok callee middle (type, finish)).mpr ⟨resultShape, resultCounter.trans same⟩⟩

theorem callResultTy_default {callee : Impl} {start finish : Nat} {type : Ty}
    (source : callResultTy callee start = .ok (type, finish)) :
    type = (callee.results[0]?).getD Ty.unit := by
  have shape := ((callResultTy_ok callee start (type, finish)).mp source).1
  rw [← Array.getElem?_toList]
  rcases shape with ⟨empty, rfl⟩ | single
  · simp [empty]
  · simp [single]

end Goose.Lower.Validation.SummaryPreservation
