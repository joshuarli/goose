import Goose.Proofs.ConstructionAcceptedEarlierRegisterCall
import Goose.Proofs.ConstructionAcceptedCalleeBodyComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_scalarLocal_prefix_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat) (scope : Nat)
    (statements : List Stmt) (expression : Expr) (summary : Summary)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (body : implementation.body = ⟨scope, statements, some expression⟩)
    (known : implementation.summary = .known summary)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (form : ScalarLocalStatements statements) (tailForm : AcceptedBinaryExpression expression)
    (scalarLocals : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  have clear : FutureGlobalsClear config caller.initialized state := source.futureGlobals
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear,
      EarlierCallerObservations.refl state.nextAct state types, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp only [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
        timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
      exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear,
        EarlierCallerObservations.refl state.nextAct state types, trivial⟩
    | succ fuel =>
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    obtain ⟨frame, phase, impl, initialized, interpretation, frameBody, cursor, frameSource, position, frameWorld,
      bodyTypes, declared, typed⟩ := acceptedZeroArgumentRegisterCallee config accepted caller state ambient types live regions pending
        target context implementation ty source world contextAt implementationAt parameters
    have scopeEmpty : frame.interpretation.environment.scopes = [] := by rw [interpretation]; rfl
    have channelEq : frame.interpretation.environment.channels = [.register ty] := by rw [interpretation]; rfl
    have bodyEq : frame.source.impl.body = ⟨scope, statements, some expression⟩ := by simpa [impl] using body
    have bodyPosition : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩) := by
      simpa [bodyEq] using position
    have effectAvailable := checked.zeroArgument_calleeFrame_effects accepted caller frame target context implementation activation origin
      ty roots typingAfter rootsAfter source.compatible frameSource.compatible contextAt implementationAt parameters summary known
      phase impl interpretation initialized frameBody
    have localScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
        frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
      intro id expression origin member descriptor present
      apply scalarLocals id expression origin member descriptor
      simpa [impl] using present
    have tailPresent : implementation.body.value.isSome = true := by simp [body, Block.value]
    obtain ⟨bodyDeclared, validatedType⟩ := validated_scalarRegister_body_typing config.module context.impl implementation
      accepted.accepted implementationAt ty results scalarTy tailPresent
    have actualType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
        .ok ([ty], declared) := by
      refine ⟨bodyDeclared, ?_⟩
      conv => lhs; rw [← frameBody]
      simpa [implementationBodyFrame, impl, body, parameters] using validatedType
    have actualParameters : frame.source.impl.params = #[] := by simpa [impl] using parameters
    obtain ⟨nextTypes, nextLive, extend, acts, scopeClocks, bodyWorld, bodyClear, observed, bodyResult⟩ :=
      execActivationBody_scalarLocal_prefix_earlier fuel config accepted frame target pushed (.callChannels activation [] :: ambient)
        types live regions pending state.nextAct scope statements expression ty frameWorld frameSource phase actualParameters scopeEmpty cursor frameBody
        bodyEq (by rw [interpretation]; exact Nat.le_refl _) channelEq bodyPosition form tailForm localScalar actualType (by simpa [bodyEq] using effectAvailable)
    have sameEnvironment : frame.interpretation.environment = activation := by rw [interpretation]; rfl
    have bodySafe : ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody fuel config activation [] implementation.body pushed
      RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
      refine ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extend, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [sameEnvironment, body] using acts
      · simpa only [sameEnvironment, body] using scopeClocks
      · simpa only [sameEnvironment, body, initialized] using bodyWorld
      · simpa only [sameEnvironment, body, initialized] using bodyClear
      · simpa only [sameEnvironment, body] using observed
      · cases execution : execActivationBody fuel config activation [] implementation.body pushed with
        | ok carriers after =>
          have execution' : execActivationBody fuel config activation [] ⟨scope, statements, some expression⟩ pushed = .ok carriers after := by simpa [body] using execution
          simp only [sameEnvironment, execution'] at bodyResult
          simp only [execution]
          exact ⟨trivial, bodyResult⟩
        | stop reason after => simp [execution]
        | escape address carriers after | jump destination kind after =>
          rw [body] at execution
          simp [sameEnvironment, execution] at bodyResult
    exact invokeCall_register_compose_earlier fuel config caller.initialized caller.interpretation.environment state ambient types live regions pending
      state.nextAct target context implementation ty origin world clear contextAt implementationAt parameters results bodySafe

theorem invokeCall_scalarLocal_prefix_earlier_frame (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat) (scope : Nat)
    (statements : List Stmt) (expression : Expr) (summary : Summary)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (body : implementation.body = ⟨scope, statements, some expression⟩)
    (known : implementation.summary = .known summary)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (form : ScalarLocalStatements statements) (tailForm : AcceptedBinaryExpression expression)
    (scalarLocals : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, observations, result⟩ :=
    invokeCall_scalarLocal_prefix_earlier fuel config accepted caller state ambient types live regions pending target context implementation ty origin
      scope statements expression summary world source contextAt implementationAt parameters results body known scalarTy form tailForm scalarLocals
      roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld,
    source.afterEarlierObservations acts scopes observations, clear, observations, result⟩

#print axioms invokeCall_scalarLocal_prefix_earlier_frame
#print axioms invokeCall_scalarLocal_prefix_earlier
end Goose.Proofs.ConstructionAcceptedExecution
