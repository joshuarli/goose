import Goose.Proofs.ConstructionAcceptedRecursiveRegisterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_registerCall_withArguments_fromInvoke (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (target : Nat) (context : Context)
    (implementation : Impl) (arguments : List Arg) (ty : Ty) (origin : Nat)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (safe : ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config environment target arguments [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue (fuel + 1) config environment (.call target arguments origin) state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, callResult⟩ := safe
  cases execution : invokeCall fuel config environment target arguments [.register ty] origin state with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at callActClock callScopeClock callWorld callClear callResult
    have evaluated : evalValue (fuel + 1) config environment (.call target arguments origin) state = .stop reason after := by
      simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution, bind, pure]
    rw [evaluated]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, trivial⟩
  | escape address carriers after | jump target kind after => simp [execution] at callResult
  | ok carriers after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at callActClock callScopeClock callWorld callClear callResult
    obtain ⟨ambientSame, value, rfl, represented⟩ := callResult
    have evaluated : evalValue (fuel + 1) config environment (.call target arguments origin) state = .ok value after := by
      simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution,
        publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
        List.mapM_cons, List.mapM_nil, List.forIn_nil, singleCarrier, carrierValue, bind, pure, Except.bind, Except.pure]
    rw [evaluated]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, callActClock, callScopeClock, callWorld, callClear, ambientSame, represented⟩


theorem evalValue_registerCall_fromInvoke (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (target : Nat) (context : Context)
    (implementation : Impl) (ty : Ty) (origin : Nat)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (safe : ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue (fuel + 1) config environment (.call target [] origin) state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact evalValue_registerCall_withArguments_fromInvoke fuel config initialized environment state ambient types regions pending
    target context implementation [] ty origin contextAt implementationAt results safe



theorem evalValue_recursive_register_withLocals (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (graph : RegisterCallGraphWithLocals config ty)
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
    have safe := invokeCall_recursive_register_withLocals fuel config accepted ty scalarTy graph caller state ambient types live regions pending
      target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
    exact evalValue_registerCall_fromInvoke fuel config caller.initialized caller.interpretation.environment state ambient types regions pending
      target context implementation ty origin contextAt implementationAt results safe

theorem evalValue_recursive_register_emptyCaller_withLocals (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (graph : RegisterCallGraphWithLocals config ty)
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
    evalValue_recursive_register_withLocals fuel config accepted caller state ambient types live regions pending target context implementation
      ty origin graph world source contextAt implementationAt parameters results scalarTy roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld,
    source.restoreEmptyVariables empty acts scopes clear, clear, result⟩


#print axioms evalValue_registerCall_withArguments_fromInvoke
#print axioms evalValue_registerCall_fromInvoke
#print axioms evalValue_recursive_register_emptyCaller_withLocals
#print axioms evalValue_recursive_register_withLocals
end Goose.Proofs.ConstructionAcceptedExecution
