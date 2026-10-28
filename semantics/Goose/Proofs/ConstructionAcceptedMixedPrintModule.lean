import Goose.Proofs.ConstructionAcceptedMixedReadsModule
import Goose.Proofs.ConstructionAcceptedMixedLocalModule
import Goose.Proofs.ConstructionByteEntryScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedModule_mixedRegisterPrint_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (statements : List Stmt) (contextId origin localId statementOrigin printOrigin : Nat) (argument : Expr)
    (helperContext : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar) (resultTy : Ty) (resultExpression : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId [.byVal argument] origin) statementOrigin, .print [.expr (.read (.var localId))] printOrigin])
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
      ∀ descriptor, helper.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  exact acceptedModule_mixedRegisterReadsPrint_fromEntry fuel config accepted original implementation statements contextId origin localId statementOrigin printOrigin [] argument helperContext helper parameter descriptor resultTy resultExpression
    globals entryTail originalAt implementationAt (by simpa [localReadStatements] using body) prefixForm prefixOwners prefixScalar localScalar
    contextAt helperAt helperParameters helperResults mode declared scalar resultScalar argumentForm helperForm helperTail resultForm helperOwners helperScalar

theorem acceptedModule_mixedRegisterPrint_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (statements : List Stmt) (contextId origin localId statementOrigin printOrigin : Nat) (argument : Expr)
    (helperContext : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar) (resultTy : Ty) (resultExpression : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId [.byVal argument] origin) statementOrigin, .print [.expr (.read (.var localId))] printOrigin])
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
      ∀ descriptor, helper.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  exact acceptedModule_mixedRegisterReadsPrint_allFuel fuel config accepted original implementation statements contextId origin localId statementOrigin printOrigin [] argument helperContext helper parameter descriptor resultTy resultExpression
    globals entryTail originalAt implementationAt (by simpa [localReadStatements] using body) prefixForm prefixOwners prefixScalar localScalar
    contextAt helperAt helperParameters helperResults mode declared scalar resultScalar argumentForm helperForm helperTail resultForm helperOwners helperScalar

#print axioms acceptedModule_mixedRegisterPrint_allFuel
#print axioms acceptedModule_mixedRegisterPrint_fromEntry
end Goose.Proofs.ConstructionAcceptedExecution
