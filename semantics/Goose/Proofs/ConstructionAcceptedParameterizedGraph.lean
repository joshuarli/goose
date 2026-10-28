import Goose.Proofs.ConstructionAcceptedParameterizedBoundTail
import Goose.Proofs.ConstructionAcceptedUnaryCallComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def ParameterizedRegisterTailGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    ∃ descriptor summary tailTarget tailOrigin tailContext tailCallee tailParameter tailDescriptor tailArgument,
      implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      (∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∧
      implementation.body = ⟨implementation.body.scope, [], some (.call tailTarget [.byVal tailArgument] tailOrigin)⟩ ∧
      config.module.contexts[tailTarget]? = some tailContext ∧
      config.module.impls[tailContext.impl]? = some tailCallee ∧
      tailCallee.params = #[tailParameter] ∧ tailParameter.mode = .byValue ∧
      tailCallee.vars[tailParameter.var]? = some tailDescriptor ∧ tailDescriptor.ty = .int integer ∧
      tailCallee.results = #[⟨.int integer, .register, none⟩] ∧
      UnaryRegisterExpression config integer tailArgument

end Goose.Proofs.ConstructionAcceptedExecution
