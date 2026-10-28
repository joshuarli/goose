import Goose.Proofs.ConstructionAcceptedArgumentListSequence
import Goose.Proofs.ConstructionAcceptedEffectfulArgumentTerminal
import Goose.Proofs.ConstructionAcceptedNestedArgumentSequence
import Goose.Proofs.ConstructionAcceptedNestedArgumentFlat

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem checkedSequence_effectfulArgumentList (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (statements : List Stmt) (localId statementOrigin : Nat)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin])
    (prefixForm : MixedLocalStatements statements)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, implementation.vars[localId]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id origin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (forms : EffectfulScalarArguments expressions)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value localOrigin, .letS localId value localOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, callee.vars[localId]? = some localDesc →
        (∃ t, localDesc.ty = .int t) ∨ localDesc.ty = .bool) :
    ∀ (sequenceFuel : Nat) (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      activation.scopes = [] →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts sequenceFuel config frame.interpretation.environment implementation.body.stmts before) := by
  apply checkedSequence_nestedArgumentList config accepted original implementation statements localId statementOrigin contextId callOrigin
    context callee expressions parameterTypes resultTy resultExpression originalAt implementationAt body prefixForm prefixOwners prefixScalar
    localScalar blockConditions ?_ contextAt calleeAt descriptors results resultScalar forms.nested bodyForm tail resultForm owners scalarOwners
  intro expression member outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
  exact ((forms.member member).notNested outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal).elim

theorem acceptedModule_effectfulArgumentList_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (statements : List Stmt) (localId statementOrigin : Nat)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (globals : ∀ globalId, globalId < config.module.globals.size →
      ∃ descriptor, config.module.globals[globalId]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin])
    (prefixForm : MixedLocalStatements statements)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, implementation.vars[localId]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id origin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (forms : EffectfulScalarArguments expressions)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value localOrigin, .letS localId value localOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, callee.vars[localId]? = some localDesc →
        (∃ t, localDesc.ty = .int t) ∨ localDesc.ty = .bool) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedModule_nestedArgumentList_allFuel fuel config accepted original implementation statements localId statementOrigin contextId callOrigin
    context callee expressions parameterTypes resultTy resultExpression globals entryTail originalAt implementationAt body prefixForm prefixOwners prefixScalar
    localScalar blockConditions ?_ contextAt calleeAt descriptors results resultScalar forms.nested bodyForm tail resultForm owners scalarOwners
  intro expression member outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
  exact ((forms.member member).notNested outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal).elim

#print axioms acceptedModule_effectfulArgumentList_allFuel
#print axioms checkedSequence_effectfulArgumentList
end Goose.Proofs.ConstructionAcceptedExecution
