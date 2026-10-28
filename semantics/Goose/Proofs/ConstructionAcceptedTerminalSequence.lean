import Goose.Proofs.ConstructionAcceptedRegisterLetPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

def StatementWorldOutcome (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : Nat) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (outcome : ExecutionStep Flow) : Prop :=
  match outcome with
  | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
      AcceptedWorld config initialized after nextAmbient nextTypes nextLive nextRegions pending
  | .ok flow after => flow = .normal .unit ∧ ∃ frame nextTypes nextLive nextRegions,
      frame.initialized = initialized ∧
      AcceptedWorld config initialized after ambient nextTypes nextLive nextRegions pending ∧
      AcceptedFrame config accepted frame after nextTypes
  | _ => False

theorem execStmts_terminal_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (environment : RuntimeActivation) (statement : Stmt) (state : ExecutionState)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (statementWorld : StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmt fuel config environment statement state)) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmts (fuel + 1) config environment [statement] state) := by
  cases executed : execStmt fuel config environment statement state with
  | stop reason after =>
    simp only [StatementWorldOutcome, executed] at statementWorld
    simpa [execStmts, bind, executed, StatementWorldOutcome] using statementWorld
  | escape target carriers after | jump target kind after => simp only [StatementWorldOutcome, executed] at statementWorld
  | ok flow after =>
    simp only [StatementWorldOutcome, executed] at statementWorld
    obtain ⟨normal, next, nextTypes, nextLive, nextRegions, initialized, nextWorld, nextSource⟩ := statementWorld
    subst flow
    cases fuel with
    | zero =>
      simp only [execStmts, bind, executed, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, nextTypes, nextLive, nextRegions, nextWorld⟩
    | succ fuel =>
      simp only [execStmts, bind, executed, pure, StatementWorldOutcome]
      exact ⟨trivial, next, nextTypes, nextLive, nextRegions, initialized, nextWorld, nextSource⟩

theorem mixedLocalRegisterParameter_terminalWorld {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin localId statementOrigin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr) (scope scopeInst : Nat) (outerScopes : List (Nat × Nat))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (mode : parameter.mode = .byValue) (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (nesting : caller.typingFuel = checkFuel + 3)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId [.byVal expression] origin) statementOrigin)))
    (localScalar : ∀ localDescriptor, caller.typing.variables[localId]? = some localDescriptor →
      (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool)
    (scopes : caller.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient)  :
    StatementWorldOutcome config accepted caller.initialized ambient pending
      (execStmt fuel config caller.interpretation.environment
        (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state) := by
  have outcome := mixedLocalRegisterParameter_position_letAllFuel shape fuel checkFuel config accepted caller state ambient types live regions pending
    contextId origin localId statementOrigin context helper parameter descriptor resultTy resultExpression scope scopeInst outerScopes
    contextAt helperAt parameters results mode resultScalar declared scalar callerInitialized world callerSource bounded nesting position
    localScalar scopes form tail resultShape owners scalarOwners depth outer
  cases executed : execStmt fuel config caller.interpretation.environment
      (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state with
  | stop reason after =>
    simp only [executed] at outcome
    obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩ := outcome
    simp only [StatementWorldOutcome, executed]
    exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, callerInitialized.symm ▸ finalWorld⟩
  | escape target carriers after | jump target kind after => simp only [executed] at outcome
  | ok flow after =>
    simp only [executed] at outcome
    obtain ⟨normal, nextTypes, nextLive, nextRegions, finalWorld, finalSource⟩ := outcome
    simp only [StatementWorldOutcome, executed]
    exact ⟨normal, advanceLocalFrame caller localId, _, _, _, rfl, finalWorld, finalSource⟩

#print axioms mixedLocalRegisterParameter_terminalWorld
#print axioms execStmts_terminal_world
end Goose.Proofs.ConstructionAcceptedExecution
