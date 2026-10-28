import Goose.Proofs.ConstructionAcceptedMixedRegisterLet
import Goose.Proofs.ConstructionAcceptedCheckedSequenceModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem checkedSequence_registerLet (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (statements : List Stmt) (contextId origin localId statementOrigin : Nat) (argument : Expr)
    (helperContext : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar) (resultTy : Ty) (resultExpression : Expr)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId [.byVal argument] origin) statementOrigin])
    (prefixForm : MixedLocalStatements statements)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, implementation.vars[localId]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (contextAt : config.module.contexts[contextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParameters : helper.params = #[parameter]) (helperResults : helper.results = #[⟨resultTy, .register, none⟩])
    (mode : parameter.mode = .byValue) (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (resultScalar : (∃ ty, resultTy = .int ty) ∨ resultTy = .bool)
    (argumentForm : AcceptedBinaryExpression argument) (helperForm : MixedLocalStatements helper.body.stmts)
    (helperTail : helper.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (helperOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperScalar : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts → AcceptedBinaryExpression expression →
      ∀ descriptor, helper.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)  :
    ∀ (sequenceFuel : Nat) (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts sequenceFuel config frame.interpretation.environment implementation.body.stmts before) := by
  intro sequenceFuel frame activation before types live regions scopeInst world source phase sourceImpl scopes position initialized limit bounded
  have fullPosition : SourcePosition accepted frame (.statements
      (statements ++ [.letS localId (.call contextId [.byVal argument] origin) statementOrigin])) := by
    simpa [body] using position
  obtain ⟨entry, entryImpl, entryAt, implAt, entryParams, entryResults⟩ := validated_entry config.module accepted.accepted
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implEq : entryImpl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  subst entryImpl
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp [sourceImpl, entryResults]
  simpa only [body] using execStmts_entryMixed_registerLet_world prefixForm argumentForm sequenceFuel config accepted frame before activation types live regions []
    contextId origin localId statementOrigin helperContext helper parameter descriptor resultTy resultExpression
    implementation.body.scope scopeInst activation.scopes contextAt helperAt helperParameters helperResults mode resultScalar declared scalar
    initialized world source phase bounded limit fullPosition scopes
    (by simpa [sourceImpl] using localScalar) (by simpa [sourceImpl] using prefixOwners)
    (by simpa [sourceImpl] using prefixScalar) unnamed helperForm helperTail resultForm helperOwners helperScalar

#print axioms checkedSequence_registerLet
end Goose.Proofs.ConstructionAcceptedExecution
