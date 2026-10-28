import Goose.Proofs.ConstructionAcceptedEarlierRecursiveCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_recursive_register_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
      source.futureGlobals, EarlierCallerObservations.refl state.nextAct state types, trivial⟩
  | succ fuel =>
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
      invokeCall_recursive_register_earlier_frame fuel config accepted ty scalarTy graph caller state ambient types live regions pending
        target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
    cases execution : invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state with
    | stop reason after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
      have evaluated : evalValue (fuel + 1) config caller.interpretation.environment (.call target [] origin) state = .stop reason after := by
        simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution, bind, pure]
      rw [evaluated]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, trivial⟩
    | escape address carriers after | jump target kind after => simp [execution] at result
    | ok carriers after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
      obtain ⟨ambientSame, value, rfl, represented⟩ := result
      have evaluated : evalValue (fuel + 1) config caller.interpretation.environment (.call target [] origin) state = .ok value after := by
        simp [evalValue, getImplementation, contextAt, implementationAt, channelsFor, results, execution,
          publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
          List.mapM_cons, List.mapM_nil, List.forIn_nil, singleCarrier, carrierValue, bind, pure, Except.bind, Except.pure]
      rw [evaluated]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, ambientSame, represented⟩

#print axioms evalValue_recursive_register_earlier
end Goose.Proofs.ConstructionAcceptedExecution
