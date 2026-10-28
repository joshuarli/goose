import Goose.Proofs.ConstructionAcceptedArithmeticCallEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem scalarBinaryCall_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {operation : Goose.Core.BinOp} {left right : Expr} {operandOrigin origin : Nat}
    {before after : RState} {roots : List RootRef} (summary : Summary)
    (form : AcceptedBinaryExpression (.bin operation left right operandOrigin))
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (clear : NoParameterAccess before.eff)
    (checked : rpExpr env (.call target [.byVal (.bin operation left right operandOrigin)] origin) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  exact arithmeticBinaryCall_noParameter (config := ⟨.release, env.mod⟩) (integer := .i64) summary
    (.operand (.scalar form)) rfl contextAt calleeAt parameters known clear checked

theorem scalarBinaryCallTail_noParameter (source : PEnv) (scope target origin operandOrigin : Nat)
    (operation : Goose.Core.BinOp) (left right : Expr) (context : Context) (callee : Impl) (parameter : Param) (summary : Summary)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (form : AcceptedBinaryExpression (.bin operation left right operandOrigin))
    (contextAt : source.mod.contexts[target]? = some context) (calleeAt : source.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary) (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, [], some (.call target [.byVal (.bin operation left right operandOrigin)] origin)⟩ before = .ok (result, after)) :
    NoParameterAccess after.eff := by
  exact arithmeticBinaryCallTail_noParameter ⟨.release, source.mod⟩ .i64 source scope target origin operandOrigin operation left right
    context callee parameter summary before after result (.operand (.scalar form)) rfl contextAt calleeAt parameters known clear rooted

#print axioms scalarBinaryCallTail_noParameter
#print axioms scalarBinaryCall_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
