import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingSourceOutputs
import Goose.Lower.Validation.EmittedTypingCallCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedSourceArgument (env : Core.TEnv) (results : List Ty) : Arg → Prop
  | .byVal expr => EmittedSourceExpression env results expr
  | .byRef _ place => EmittedSourcePlace env results place

theorem emitted_source_arguments {env : Core.TEnv} {results : List Ty} (args : List Arg)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (children : ∀ arg ∈ args, EmittedSourceArgument env results arg)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerArgs args (lowerEnv env.mod env.vars results) before).2 := by
  induction args generalizing params start before with
  | nil => exact builder
  | cons arg args inductionHypothesis =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      have restLength : params.length = args.length := by simpa using sameLength
      cases arg with
      | byVal expr =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
          tyArgs_byVal_head source
        have child : EmittedSourceExpression env results expr := children (.byVal expr) (by simp)
        have childBuilder := child childSource generated builder
        have childGenerated : GeneratedBuilderState
            (lowerExpr expr (lowerEnv env.mod env.vars results) before).2 := generated.lowerExpr expr rfl
        exact inductionHypothesis restLength restSource
          (fun arg member => children arg (by simp [member])) childGenerated childBuilder
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        have child : EmittedSourcePlace env results place := children (.byRef mu place) (by simp)
        have placeBuilder := child placeSource generated builder
        have childBuilder := emitted_checked_lowerArg_byRef mu place placeBuilder
        have childGenerated : GeneratedBuilderState
            (lowerArg (.byRef mu place) (lowerEnv env.mod env.vars results) before).2 := generated.lowerArg _ rfl
        exact inductionHypothesis restLength restSource
          (fun arg member => children arg (by simp [member])) childGenerated childBuilder

theorem emitted_source_call {env : Core.TEnv} {results : List Ty}
    (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, EmittedSourceArgument env results arg) :
    EmittedSourceExpression env results (.call context args origin) := by
  intro type start finish source initial before generated builder
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt,
    length, argsSource, resultSource⟩ := tyExpr_call_tables source
  have arguments := emitted_source_arguments args length argsSource children generated builder
  apply emitted_checked_lowerExpr_call source results arguments
  intro foundCtx foundCallee foundCtxAt foundCalleeAt block active
  rw [contextAt] at foundCtxAt
  cases Option.some.inj foundCtxAt
  rw [calleeAt] at foundCalleeAt
  cases Option.some.inj foundCalleeAt
  exact lowerArgs_generated_typed args length argsSource rfl (by simp [active]) generated

end Goose.Lower.Validation
