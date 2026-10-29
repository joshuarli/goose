import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveCallTail
import Goose.Proofs.ConstructionAcceptedRecursiveArgumentEvaluation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def RecursiveParameterTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Prop :=
  ∃ descriptor summary target origin context callee parameter tailDescriptor tailSummary argument,
    implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧ implementation.summary = .known summary ∧
    implementation.body = ⟨implementation.body.scope, [], some (.call target [.byVal argument] origin)⟩ ∧
    config.module.contexts[target]? = some context ∧ config.module.impls[context.impl]? = some callee ∧
    callee.params = #[parameter] ∧ parameter.mode = .byValue ∧ callee.vars[parameter.var]? = some tailDescriptor ∧
    tailDescriptor.ty = .int integer ∧ callee.results = #[⟨.int integer, .register, none⟩] ∧
    callee.summary = .known tailSummary ∧ RecursiveArgumentExpression config integer implementation argument

def RecursiveParameterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      RecursiveParameterTailCallee config integer implementation

end Goose.Proofs.ConstructionAcceptedExecution
