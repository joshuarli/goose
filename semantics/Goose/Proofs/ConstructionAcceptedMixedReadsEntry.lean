import Goose.Proofs.ConstructionAcceptedMixedRegisterReads
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
  obtain ⟨frame, activation, initialEq, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements_withInitialized config accepted state [] (declaredRootTypes config.module) live [] [] world
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have depth : state.activations.length < Goose.Core.maxCallDepth := by
    have runtime := world.ownership.runtime.activations
    cases active : state.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  have canonical : activation = ⟨original.impl, state.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars' scopes' channels' =>
      simp only at implId act vars scopes channels
      cases implId
      cases act
      cases vars
      cases scopes
      cases channels
      rfl
  have step := entryCallStep (fuel + 1) config ⟨0, 0, #[], [], []⟩ state original frame.source.impl originalAt implAt
    parameters results depth
  simp only [Nat.add_assoc] at step
  rw [← canonical] at step
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implId]
    exact implAt
  have entryAction : enterActivation (fuel + 2) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [entryAction] at step
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  let full := entryFrame
  let types := declaredRootTypes config.module
  have fullSource : AcceptedFrame config accepted full before types := source
  have fullWorld : AcceptedWorld config full.initialized before [.callChannels activation []] types live [] [] := frameWorld
  have initialized : full.initialized = config.module.globals.size := by
    simpa only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initialEq
  have limit : full.typing.globalLimit ≤ config.module.globals.size := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded full.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, full, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame, parameters]
  have fullPosition : SourcePosition accepted full (.statements
      (statements ++ (.letS localId (.call contextId [.byVal argument] origin) statementOrigin :: (localReadStatements localId readOrigins ++ [.print [.expr (.read (.var localId))] printOrigin])))) := by
    simpa [full, implementationEq, body] using position
  have sourceImpl : full.source.impl = implementation := by
    simpa [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using implementationEq
  have frameScopes : full.interpretation.environment.scopes =
      (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq]
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (full.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  have outcome := execStmts_entryMixed_registerReadsPrint_world prefixForm argumentForm fuel config accepted full before activation types live [] []
    contextId origin localId statementOrigin printOrigin readOrigins helperContext helper parameter descriptor resultTy resultExpression
    frame.source.impl.body.scope activated.nextScope activation.scopes contextAt helperAt helperParameters helperResults mode resultScalar declared scalar
    initialized fullWorld fullSource phase initialBound limit fullPosition frameScopes
    (by simpa [sourceImpl] using localScalar) (by simpa [sourceImpl] using prefixOwners) (by simpa [sourceImpl] using prefixScalar) unnamed
    helperForm helperTail resultForm helperOwners helperScalar
  refine ⟨frame, activation, channels, implementationEq, environmentEq, initialized, step, ?_⟩
  simpa [full, entryFrame, activated, before, implementationEq, body] using outcome

#print axioms acceptedEntry_mixedRegisterReadsPrint
end Goose.Proofs.ConstructionAcceptedExecution
