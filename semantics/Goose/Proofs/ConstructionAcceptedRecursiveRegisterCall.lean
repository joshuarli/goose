import Goose.Proofs.ConstructionAcceptedRegisterCallCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def RegisterCalleeForm (config : EvalConfig) (ty : Ty) (implementation : Impl) : Prop :=
  ∃ summary, implementation.summary = .known summary ∧
    ((∃ scope statements expression,
      implementation.body = ⟨scope, statements, some expression⟩ ∧ ScalarLocalStatements statements ∧
      AcceptedBinaryExpression expression ∧
      ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
        implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) ∨
     (∃ scope target origin context callee,
      implementation.body = ⟨scope, [], some (.call target [] origin)⟩ ∧
      config.module.contexts[target]? = some context ∧ config.module.impls[context.impl]? = some callee ∧
      callee.params = #[] ∧ callee.results = #[⟨ty, .register, none⟩]))

def RegisterCallGraph (config : EvalConfig) (ty : Ty) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl), config.module.contexts[target]? = some context →
    config.module.impls[context.impl]? = some implementation → implementation.params = #[] →
    implementation.results = #[⟨ty, .register, none⟩] → RegisterCalleeForm config ty implementation

theorem invokeCall_recursive_register (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (ty : Ty) (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (graph : RegisterCallGraph config ty) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (origin : Nat)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro caller state ambient types live regions pending target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
    obtain ⟨summary, known, form | form⟩ := graph target context implementation contextAt implementationAt parameters results
    · obtain ⟨scope, statements, expression, body, statementsForm, tailForm, locals⟩ := form
      exact invokeCall_scalarLocal_prefix fuel config accepted caller state ambient types live regions pending target context implementation ty origin
        scope statements expression summary world source contextAt implementationAt parameters results body known scalar statementsForm tailForm locals
        roots typingAfter rootsAfter checked
    · obtain ⟨scope, innerTarget, innerOrigin, innerContext, innerCallee, body, innerContextAt, innerCalleeAt, innerParameters, innerResults⟩ := form
      cases fuel with
      | zero =>
        simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, trivial⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          simp only [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
            timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
          exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, trivial⟩
        | succ fuel =>
          let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
          let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
          obtain ⟨frame, phase, impl, initialized, interpretation, frameBody, cursor, frameSource, position, frameWorld,
            bodyTypes, declared, typed⟩ := acceptedZeroArgumentRegisterCallee config accepted caller state ambient types live regions pending
              target context implementation ty source world contextAt implementationAt parameters
          have scopes : frame.interpretation.environment.scopes = [] := by rw [interpretation]; rfl
          have channels : frame.interpretation.environment.channels = [.register ty] := by rw [interpretation]; rfl
          have bodyEq : frame.source.impl.body = ⟨scope, [], some (.call innerTarget [] innerOrigin)⟩ := by simpa [impl] using body
          have bodyPosition : SourcePosition accepted frame (.block ⟨scope, [], some (.call innerTarget [] innerOrigin)⟩) := by simpa [bodyEq] using position
          have actualParameters : frame.source.impl.params = #[] := by simpa [impl] using parameters
          have requests : frame.typing.resultRequests = [.register] := by
            have equal := congrArg (fun f : ConstructionSourceFrame => f.typing.resultRequests) frameBody
            simpa [implementationBodyFrame, impl, results] using equal.symm
          have typingModule : frame.typing.module = config.module := by
            have equal := congrArg (fun f : ConstructionSourceFrame => f.typing.module) frameBody
            simpa [implementationBodyFrame] using equal.symm
          have checkedEffects := checked.zeroArgument_calleeFrame_effects accepted caller frame target context implementation activation origin
            ty roots typingAfter rootsAfter source.compatible frameSource.compatible contextAt implementationAt parameters summary known
            phase impl interpretation initialized frameBody
          have frameEnv : frame.interpretation.environment = activation := by rw [interpretation]; rfl
          have bodySafe : ∃ nextTypes nextLive nextAmbient,
              let outcome := execActivationBody fuel config activation [] implementation.body pushed
              RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
              pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
              AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
              FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
              (match outcome with
               | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
                  ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
               | .stop .. => True | .escape .. | .jump .. => False) := by
            cases fuel with
            | zero =>
              simp only [execActivationBody, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
              exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, initialized ▸ frameWorld, initialized ▸ frameSource.futureGlobals, trivial⟩
            | succ fuel =>
              cases fuel with
              | zero =>
                obtain ⟨scopeWorld, scopeSource, _⟩ := acceptedCalleeBodyScope config accepted frame target pushed
                  (.callChannels activation [] :: ambient) types live regions pending frameWorld frameSource phase actualParameters scopes cursor
                rw [bodyEq] at scopeWorld scopeSource
                simp only [Block.scope] at scopeWorld scopeSource
                rw [body]
                simp only [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll,
                  List.forIn_nil, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
                exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_succ _,
                  (by simpa [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, frameEnv, ownershipResultScopeState, initialized] using scopeWorld),
                  (by simpa [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, frameEnv, ownershipResultScopeState, initialized, FutureGlobalsClear] using scopeSource.futureGlobals), trivial⟩
              | succ fuel =>
                have safe := execActivationBody_checked_registerCall_compose fuel config accepted frame target pushed
                  (.callChannels activation [] :: ambient) types live regions pending scope innerTarget innerOrigin innerContext innerCallee ty
                  frameWorld frameSource phase actualParameters scopes cursor frameBody bodyEq channels bodyPosition
                  (by simpa [typingModule] using innerContextAt) (by simpa [typingModule] using innerCalleeAt) innerResults scalar requests
                  (by simpa [bodyEq] using checkedEffects)
                  (by
                    intro r t ra innerChecked scopedWorld scopedSource
                    have recur := ih fuel (by omega) (entryStatementsFrame config frame pushed.nextScope)
                      (ownershipResultScopeState frame.interpretation.environment scope pushed)
                      (.callChannels activation [] :: ambient) types live regions pending innerTarget innerContext innerCallee innerOrigin
                      scopedWorld scopedSource innerContextAt innerCalleeAt innerParameters innerResults r t ra innerChecked
                    obtain ⟨nt, nl, na, ext, ac, sc, w, cl, res⟩ := recur
                    refine ⟨nt, nl, na, ext, ?_, ?_, ?_, ?_, ?_⟩
                    · simpa only [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, RootInterpretation.enterScope] using ac
                    · simpa only [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, RootInterpretation.enterScope] using sc
                    · simpa only [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, RootInterpretation.enterScope] using w
                    · simpa only [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, RootInterpretation.enterScope] using cl
                    · simp only [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, RootInterpretation.enterScope] at res
                      cases execution : invokeCall fuel config
                        { frame.interpretation.environment with scopes := (scope, pushed.nextScope) :: frame.interpretation.environment.scopes }
                        innerTarget [] [.register ty] innerOrigin (ownershipResultScopeState frame.interpretation.environment scope pushed) <;>
                        simpa [execution] using res
)
                have fuelEq : fuel + 2 = fuel + 1 + 1 := by omega
                obtain ⟨nt, nl, na, ext, ac, sc, w, cl, res⟩ := safe
                refine ⟨nt, nl, na, ext, ?_, ?_, ?_, ?_, ?_⟩
                · simpa only [frameEnv, body, initialized, fuelEq] using ac
                · simpa only [frameEnv, body, initialized, fuelEq] using sc
                · simpa only [frameEnv, body, initialized, fuelEq] using w
                · simpa only [frameEnv, body, initialized, fuelEq] using cl
                · simp only [frameEnv, body, initialized, fuelEq] at res
                  cases execution : execActivationBody (fuel + 1 + 1) config activation []
                    ⟨scope, [], some (.call innerTarget [] innerOrigin)⟩ pushed <;>
                    simpa [body, execution] using res

          exact invokeCall_register_compose fuel config caller.initialized caller.interpretation.environment state ambient types live regions pending
            target context implementation ty origin world source.futureGlobals contextAt implementationAt parameters results bodySafe

theorem evalValue_recursive_register (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (graph : RegisterCallGraph config ty)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config caller.interpretation.environment (.call target [] origin) state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, trivial⟩
  | succ fuel =>
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, callResult⟩ :=
      invokeCall_recursive_register fuel config accepted ty scalarTy graph caller state ambient types live regions pending
        target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
    cases execution : invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state with
    | stop reason after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at callActClock callScopeClock callWorld callClear callResult
      have evaluated : evalValue (fuel + 1) config caller.interpretation.environment (.call target [] origin) state = .stop reason after := by
        simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution, bind, pure]
      rw [evaluated]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, trivial⟩
    | escape address carriers after | jump target kind after => simp [execution] at callResult
    | ok carriers after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at callActClock callScopeClock callWorld callClear callResult
      obtain ⟨ambientSame, value, rfl, represented⟩ := callResult
      have evaluated : evalValue (fuel + 1) config caller.interpretation.environment (.call target [] origin) state = .ok value after := by
        simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution,
          publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
          List.mapM_cons, List.mapM_nil, List.forIn_nil, singleCarrier, carrierValue, bind, pure, Except.bind, Except.pure]
      rw [evaluated]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, ambientSame, represented⟩


theorem evalValue_recursive_register_emptyCaller (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (graph : RegisterCallGraph config ty)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (empty : caller.interpretation.environment.vars = #[])
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config caller.interpretation.environment (.call target [] origin) state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩ :=
    evalValue_recursive_register fuel config accepted caller state ambient types live regions pending target context implementation
      ty origin graph world source contextAt implementationAt parameters results scalarTy roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld,
    source.restoreEmptyVariables empty acts scopes clear, clear, result⟩


#print axioms evalValue_recursive_register_emptyCaller
#print axioms evalValue_recursive_register
#print axioms invokeCall_recursive_register
end Goose.Proofs.ConstructionAcceptedExecution
