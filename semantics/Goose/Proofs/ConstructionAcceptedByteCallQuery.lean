import Goose.Proofs.ConstructionAcceptedByteCallBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem byteCall_ordinaryProducerCount (fuel : Nat) (config : EvalConfig) (caller : RuntimeActivation)
    (contextId : Nat) (origin : Goose.Core.OriginId) (context : Context) (helper : Impl)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩]) :
    ordinaryProducerCount? fuel ⟨config.module, caller.vars⟩ (.call contextId [] origin) = none := by
  cases fuel with
  | zero => simp [ordinaryProducerCount?, producerCount?, literalCount, expressionQueryBudget,
      expressionResultTypes?, contextAt, helperAt, results]
  | succ fuel => simp [ordinaryProducerCount?, producerCount?, literalCount, expressionQueryBudget,
      expressionResultTypes?, contextAt, helperAt, results]

#print axioms byteCall_ordinaryProducerCount
end Goose.Proofs.ConstructionAcceptedExecution
