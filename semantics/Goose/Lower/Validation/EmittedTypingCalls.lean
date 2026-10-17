import Goose.Lower.Validation.EmittedTypingOperations
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_call {le : LEnv} {before : LS} {function : FnId} {callee : Core.Impl}
    {params : List Ty} {values : List ValueId} {type : Ty} {start finish : Nat}
    (signature : le.sigs[function]? = some (params, callee.results.toList))
    (typed : PassableValues before params values)
    (source : Core.callResultTy callee start = .ok (type, finish)) (origin : OriginId) :
    EmittedAt le before (emitDef (.call function values (some origin))) :=
  .emit .refl _ (.data type) (call_resultTy_of_passable signature typed source origin)

theorem emitted_lowerExpr_call {env : Core.TEnv} {context : ContextId} {args : List Arg}
    {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (type, finish))
    (results : List Ty) (before : LS)
    (arguments : EmittedAt (lowerEnv env.mod env.vars results) before (lowerArgs args))
    (passing : ∀ ctx callee, env.mod.contexts[context]? = some ctx → env.mod.impls[ctx.impl]? = some callee →
      ∀ block, (lowerArgs args (lowerEnv env.mod env.vars results) before).2.cur = some block →
      PassableValues (lowerArgs args (lowerEnv env.mod env.vars results) before).2
        (callee.params.toList.map (tyOfVar callee ·.var))
        (lowerArgs args (lowerEnv env.mod env.vars results) before).1) :
    EmittedAt (lowerEnv env.mod env.vars results) before (lowerExpr (.call context args origin)) := by
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt,
    length, argsSource, resultSource⟩ := tyExpr_call_tables source
  simp only [lowerExpr]
  apply arguments.bind
  apply EmittedAt.bind
  · apply EmittedAt.emitDef
    intro live
    cases current : (lowerArgs args (lowerEnv env.mod env.vars results) before).2.cur with
    | none => simp [current] at live
    | some block =>
      exact ⟨.data type, call_resultTy_of_passable
        (lower_context_sigs_at env.vars results contextAt calleeAt)
        (passing ctx callee contextAt calleeAt block current) resultSource origin⟩
  · apply (EmittedAt.read _ _).bind
    split
    · exact (EmittedAt.emitTerm _ _ .unreachable).bind (EmittedAt.pure _ _ _)
    · exact EmittedAt.pure _ _ _

end Goose.Lower.Validation
