import Goose.Proofs.ConstructionAcceptedParameterizedBoundTail
import Goose.Proofs.ConstructionAcceptedUnaryCallComplete
import Goose.Proofs.ConstructionAcceptedRecursiveRegisterArithmetic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def ParameterizedTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) (argumentForm : Expr → Prop) : Prop :=
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
    argumentForm tailArgument


def ParameterizedLocalSummaryTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) (argumentForm : Expr → Prop) : Prop :=
  ∃ descriptor summary tailTarget tailOrigin tailContext tailCallee tailParameter tailDescriptor tailArgument,
    implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
    implementation.summary = .known summary ∧
    ((∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∨
      (tailArgument = .read (.var 0) ∧ ∃ tailSummary, tailCallee.summary = .known tailSummary)) ∧
    implementation.body = ⟨implementation.body.scope, [], some (.call tailTarget [.byVal tailArgument] tailOrigin)⟩ ∧
    config.module.contexts[tailTarget]? = some tailContext ∧
    config.module.impls[tailContext.impl]? = some tailCallee ∧
    tailCallee.params = #[tailParameter] ∧ tailParameter.mode = .byValue ∧
    tailCallee.vars[tailParameter.var]? = some tailDescriptor ∧ tailDescriptor.ty = .int integer ∧
    tailCallee.results = #[⟨.int integer, .register, none⟩] ∧
    argumentForm tailArgument

def ParameterizedScalarSummaryTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) (argumentForm : Expr → Prop) : Prop :=
  ∃ descriptor summary tailTarget tailOrigin tailContext tailCallee tailParameter tailDescriptor tailArgument,
    implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
    implementation.summary = .known summary ∧
    ((∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∨
      ((tailArgument = .read (.var 0) ∨
        ∃ operation left right origin, tailArgument = .bin operation left right origin ∧
          AcceptedBinaryExpression (.bin operation left right origin)) ∧
        ∃ tailSummary, tailCallee.summary = .known tailSummary)) ∧
    implementation.body = ⟨implementation.body.scope, [], some (.call tailTarget [.byVal tailArgument] tailOrigin)⟩ ∧
    config.module.contexts[tailTarget]? = some tailContext ∧
    config.module.impls[tailContext.impl]? = some tailCallee ∧
    tailCallee.params = #[tailParameter] ∧ tailParameter.mode = .byValue ∧
    tailCallee.vars[tailParameter.var]? = some tailDescriptor ∧ tailDescriptor.ty = .int integer ∧
    tailCallee.results = #[⟨.int integer, .register, none⟩] ∧
    argumentForm tailArgument

def ParameterizedRegisterTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Prop :=
  ParameterizedTailCallee config integer implementation (UnaryRegisterExpression config integer)

def ParameterizedRegisterTailGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] → ParameterizedRegisterTailCallee config integer implementation

def ParameterizedRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
      ParameterizedRegisterTailCallee config integer implementation

theorem ParameterizedRegisterTailGraph.toGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedRegisterTailGraph config integer) : ParameterizedRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  exact Or.inr (graph target context implementation parameter contextAt implementationAt parameters mode results)

def ParameterizedScalarRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      (∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      ParameterizedRegisterTailCallee config integer implementation

theorem ParameterizedRegisterGraph.toScalarGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedRegisterGraph config integer) : ParameterizedScalarRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | tail
  · exact Or.inl identity
  · exact Or.inr (Or.inr tail)

def ParameterizedArithmeticTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Prop :=
  ParameterizedTailCallee config integer implementation (RegisterArithmeticExpression config integer)

def ParameterizedArithmeticRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      (∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      ParameterizedArithmeticTailCallee config integer implementation

def ParameterizedSummaryRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      ParameterizedArithmeticTailCallee config integer implementation

def ParameterizedLocalSummaryRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      ParameterizedLocalSummaryTailCallee config integer implementation (RegisterArithmeticExpression config integer)

def ParameterizedScalarSummaryRegisterGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      ParameterizedScalarSummaryTailCallee config integer implementation (RegisterArithmeticExpression config integer)

theorem ParameterizedLocalSummaryRegisterGraph.toScalarSummaryGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedLocalSummaryRegisterGraph config integer) : ParameterizedScalarSummaryRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalar | tail
  · exact Or.inl identity
  · exact Or.inr (Or.inl scalar)
  · obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, certificate, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailForm⟩ := tail
    have certificate' : (∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) ∨
        ((tailArgument = .read (.var 0) ∨ ∃ operation left right origin, tailArgument = .bin operation left right origin ∧
          AcceptedBinaryExpression (.bin operation left right origin)) ∧ ∃ tailSummary, tailCallee.summary = .known tailSummary) := by
      rcases certificate with noParameters | ⟨same, tailSummary, tailKnown⟩
      · exact Or.inl noParameters
      · exact Or.inr ⟨Or.inl same, tailSummary, tailKnown⟩
    exact Or.inr (Or.inr ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, certificate', body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailForm⟩)

theorem ParameterizedSummaryRegisterGraph.toLocalSummaryGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedSummaryRegisterGraph config integer) : ParameterizedLocalSummaryRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalar | tail
  · exact Or.inl identity
  · exact Or.inr (Or.inl scalar)
  · obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, noParameters, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailForm⟩ := tail
    exact Or.inr (Or.inr ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, Or.inl noParameters, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailForm⟩)

theorem ParameterizedArithmeticRegisterGraph.toSummaryGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedArithmeticRegisterGraph config integer) : ParameterizedSummaryRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalar | tail
  · exact Or.inl identity
  · obtain ⟨descriptor, summary, expression, declared, descriptorTy, known, noParameters, body, form⟩ := scalar
    exact Or.inr (Or.inl ⟨descriptor, summary, expression, declared, descriptorTy, known, body, form⟩)
  · exact Or.inr (Or.inr tail)

theorem ParameterizedScalarRegisterGraph.toArithmeticGraph {config : EvalConfig} {integer : Goose.Core.IntTy}
    (graph : ParameterizedScalarRegisterGraph config integer) : ParameterizedArithmeticRegisterGraph config integer := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalar | tail
  · exact Or.inl identity
  · exact Or.inr (Or.inl scalar)
  · obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, noParameters, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailForm⟩ := tail
    exact Or.inr (Or.inr ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
      declared, descriptorTy, known, noParameters, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, .operand tailForm⟩)

#print axioms ParameterizedScalarRegisterGraph.toArithmeticGraph
#print axioms ParameterizedRegisterGraph.toScalarGraph
#print axioms ParameterizedRegisterTailGraph.toGraph

end Goose.Proofs.ConstructionAcceptedExecution
