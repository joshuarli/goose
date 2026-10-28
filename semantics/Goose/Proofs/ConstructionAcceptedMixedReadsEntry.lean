import Goose.Proofs.ConstructionAcceptedRegisterReadsContract
import Goose.Proofs.ConstructionMixedLocalEntryReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedEntry_mixedRegisterReadsPrint (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) (original : Context) (implementation : Impl)
    (statements : List Stmt) (contextId origin localId statementOrigin printOrigin : Nat) (readOrigins : List Goose.Core.OriginId) (argument : Expr)
    (helperContext : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar) (resultTy : Ty) (resultExpression : Expr)
    (world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ (.letS localId (.call contextId [.byVal argument] origin) statementOrigin :: (localReadStatements localId readOrigins ++ [.print [.expr (.read (.var localId))] printOrigin])))
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
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      activation.channels = [] ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      entryFrame.initialized = config.module.globals.size ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      StatementWorldOutcome config accepted entryFrame.initialized [.callChannels activation []] []
        (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before) := by
  have sequence := checkedSequence_registerReadsPrint config accepted original implementation statements contextId origin localId statementOrigin printOrigin readOrigins argument
    helperContext helper parameter descriptor resultTy resultExpression originalAt implementationAt body prefixForm prefixOwners prefixScalar
    localScalar contextAt helperAt helperParameters helperResults mode declared scalar resultScalar argumentForm helperForm helperTail resultForm
    helperOwners helperScalar
  exact acceptedEntry_checkedSequence fuel config accepted state live original implementation world originalAt implementationAt (sequence fuel)

#print axioms acceptedEntry_mixedRegisterReadsPrint
end Goose.Proofs.ConstructionAcceptedExecution
