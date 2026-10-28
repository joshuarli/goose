import Goose.Proofs.ConstructionAcceptedStatefulTwoParameterBody
import Goose.Proofs.ConstructionAcceptedRegisterResultBody
import Goose.Proofs.ConstructionAcceptedFreshActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem statefulTwoParameter_call_world {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel checkFuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (first second : Param)
    (firstDescriptor secondDescriptor : LocalVar) (scope id origin blockOrigin : Nat) (expression : Expr)
    (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr) (resultTy : Ty) (resultExpression : Expr)
    (form : AcceptedBinaryExpression expression) (rightForm : AcceptedBinaryExpression right)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[0]? = some firstDescriptor) (secondDeclared : callee.vars[1]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value localOrigin, .letS localId value localOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, callee.vars[localId]? = some localDesc →
        (∃ t, localDesc.ty = .int t) ∨ localDesc.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin)))
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    match invokeCall fuel config frame.interpretation.environment contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] [.register resultTy] callOrigin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, (fun _ _ found => found), initialized ▸ world⟩
  | succ fuel =>
    obtain ⟨rightFrame, sameInterpretation, sameInitialized, arguments⟩ :=
      evalArguments_statefulTwoParameter_body fuel checkFuel frame state ambient types live regions pending contextId callOrigin context callee
        first second firstDescriptor secondDescriptor scope id origin blockOrigin expression intTy literal right resultTy form rightForm
        world source contextAt calleeAt parameters firstMode secondMode firstDeclared secondDeclared firstScalar secondScalar
        initialized fresh absent nesting position globalScalar
    cases evaluated : evalArguments fuel config frame.interpretation.environment callee.vars [first, second]
        [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state with
    | escape address carriers after | jump target kind after => simp [evaluated] at arguments
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      simp [invokeCall, getImplementation, contextAt, calleeAt, results, parameters, evaluated, bind, pure]
      exact ⟨ambient, types, (fun _ _ found => found), live, regions, initialized ▸ arguments.1⟩
    | ok values argumentState =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      obtain ⟨argumentWorld, callerSource, firstValue, secondValue, valuesEq, helperFrame, activation, boundState,
        helperEq, helperInitialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep,
        bound, boundExtended, boundWorld, boundSource, bodyPosition⟩ := arguments
      subst values
      by_cases tooDeep : argumentState.activations.length ≥ Goose.Core.maxCallDepth
      · simp [invokeCall, getImplementation, contextAt, calleeAt, results, parameters, evaluated, bind, pure, tooDeep, EvalM.get, timeout, EvalM.stop]
        exact ⟨ambient, types, (fun _ _ found => found), live, regions, initialized ▸ argumentWorld⟩
      · cases fuel with
        | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
        | succ fuel =>
          cases fuel with
          | zero =>
            cases expressionStep : evalValue 0 config frame.interpretation.environment
              (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state <;>
              simp [evalArguments, expressionStep, bind, timeout, EvalM.stop] at evaluated
          | succ fuel =>
            let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
            have bodyResult := mixedLocal_registerResultBody_world fuel config accepted helperFrame activation
              [(first.var, firstValue), (second.var, secondValue)] pushed boundState ambient
              (registerRootType (registerRootType types (.local activation.act argumentState.nextScope 0) firstDescriptor.ty)
                (.local activation.act argumentState.nextScope 1) secondDescriptor.ty)
              (fun other => other = .local activation.act argumentState.nextScope 1 ∨ other = .local activation.act argumentState.nextScope 0 ∨ live other)
              regions pending contextId context callee resultTy resultExpression calleeAt helperEq phase environment channels results resultScalar
              tail resultForm helperInitialized (by simpa [pushed] using bound) (by simpa [pushed] using boundWorld)
              (by simpa [pushed] using boundSource) (by simpa [pushed] using bodyPosition) bodyForm owners scalarOwners
            have implementationId : activation.implementation = context.impl := by
              have originFact := boundSource.compatible.origin
              unfold SourceOrigin at originFact
              simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, phase] at originFact
              obtain ⟨selected, calls, selectedAt, implementationAt, implementationId, rest⟩ := originFact
              have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
              subst selected
              simpa [environment, RootInterpretation.enterScope] using implementationId
            have vars : activation.vars = callee.vars := by
              have fact := boundSource.compatible.variables.trans boundSource.compatible.sourceVariables.symm
              simpa [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
                RootInterpretation.enterScope, environment, helperEq] using fact
            have activationEq : activation = ⟨context.impl, argumentState.nextAct, callee.vars, [], [.register resultTy]⟩ := by
              cases activation with
              | mk implementation actualAct actualVars actualScopes actualChannels =>
                simp only at implementationId act vars scopes channels
                cases implementationId; cases act; cases vars; cases scopes; cases channels; rfl
            have evaluated' : evalArguments (fuel + 2) config frame.interpretation.environment callee.vars [first, second]
                [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state =
                .ok [firstValue, secondValue] argumentState := by simpa [Nat.add_assoc] using evaluated
            have invokeStep : invokeCall (fuel + 3) config frame.interpretation.environment contextId
                [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right]
                [.register resultTy] callOrigin state =
                (finishActivation config.layout activation [resultTy] callOrigin
                  (execActivationBody (fuel + 1) config activation [(first.var, firstValue), (second.var, secondValue)] helperFrame.source.impl.body) >>= fun carriers =>
                    deliverCarriers (fuel + 2) config.layout [.register resultTy] carriers callOrigin) pushed := by
              simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated', parameters, enterActivation,
                freshAct, EvalM.get, EvalM.set, bind, pure, tooDeep, activationEq, pushed, helperEq]
            rw [invokeStep]
            rw [← helperEq] at bodyResult
            cases body : execActivationBody (fuel + 1) config activation [(first.var, firstValue), (second.var, secondValue)] helperFrame.source.impl.body pushed with
            | escape address carriers after | jump target kind after => simp [body] at bodyResult
            | stop reason after =>
              simp only [body] at bodyResult
              obtain ⟨nextTypes, nextLive, nextRegions, bodyExtended, bodyProtected, finalWorld⟩ := bodyResult
              simp only [bind, finishActivation, body]
              exact ⟨.callChannels activation [] :: ambient, nextTypes, nextLive, nextRegions,
                (fun root ty found => bodyExtended root ty (boundExtended root ty found)), finalWorld⟩
            | ok carriers after =>
              simp only [body] at bodyResult
              obtain ⟨returned, nextTypes, nextLive, nextRegions, equal, represented, bodyExtended, bodyProtected, finalWorld⟩ := bodyResult
              subst carriers
              have outer := (initialized ▸ argumentWorld).freshActivationOutside config config.module.globals.size argumentState ambient types live regions pending
              have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
              have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient nextTypes nextLive nextRegions pending outer'
              simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
              exact ⟨returned, rfl, represented, nextTypes,
                (fun root ty found => bodyExtended root ty (boundExtended root ty found)), nextLive, nextRegions, finished⟩

#print axioms statefulTwoParameter_call_world
end Goose.Proofs.ConstructionAcceptedExecution
