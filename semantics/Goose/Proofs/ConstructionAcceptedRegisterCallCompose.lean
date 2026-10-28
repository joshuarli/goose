import Goose.Proofs.ConstructionAcceptedRegisterCallTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_register_compose (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (clear : FutureGlobalsClear config initialized state)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (bodySafe :
      let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
      let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      ∃ nextTypes nextLive nextAmbient,
        let outcome := execActivationBody fuel config activation [] implementation.body pushed
        RootTypesExtend types nextTypes ∧
        pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
             ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True
         | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall (fuel + 2) config environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  have transition := invokeCall_zeroArgument_register_transition fuel config environment target context
    implementation ty origin state contextAt implementationAt parameters results
  by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth
  · simp only [depth, ↓reduceIte] at transition
    rw [transition]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear, trivial⟩
  · simp only [depth, ↓reduceIte] at transition
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody fuel config activation [] implementation.body pushed; _ at bodySafe
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, bodyWorld, bodyClear, bodyResult⟩ := bodySafe
    have calleeAt : config.module.impls[activation.implementation]? = some implementation := by
      simpa [activation] using implementationAt
    cases execution : execActivationBody fuel config activation [] implementation.body pushed with
    | stop reason after =>
      simp only [activation, pushed] at execution
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyResult
      have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed = .stop reason after := by
        simp [enterActivation, calleeAt, finishActivation, activation, pushed, execution]
      have callRun : invokeCall (fuel + 2) config environment target [] [.register ty] origin state = .stop reason after := by
        rw [transition]
        change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                   deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = _
        simp only [bind, entered]
      rw [callRun]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, bodyWorld, bodyClear, trivial⟩
    | escape address carriers after | jump destination kind after =>
      simp only [activation, pushed] at execution
      simp [execution] at bodyResult
    | ok carriers after =>
      simp only [activation, pushed] at execution
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyResult
      obtain ⟨rfl, value, rfl, represented⟩ := bodyResult
      have finished := finishActivation_register_normal config initialized activation ambient nextTypes nextLive regions pending
        ty origin (execActivationBody fuel config activation [] implementation.body) pushed after value
        rfl execution bodyWorld bodyClear
      obtain ⟨finishedRun, finishedWorld, finishedClear⟩ := finished
      have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed =
          .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
        simpa [enterActivation, calleeAt, results] using finishedRun
      have callRun : invokeCall (fuel + 2) config environment target [] [.register ty] origin state =
          .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
        rw [transition]
        change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                   deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = _
        simpa only [bind, entered] using deliverCarriers_register (fuel + 1) config ty value origin
          { after with activations := after.activations.filter (fun current => current.act != activation.act) }
      rw [callRun]
      exact ⟨nextTypes, nextLive, ambient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, finishedWorld,
        finishedClear, rfl, value, rfl, represented⟩

#print axioms invokeCall_register_compose
end Goose.Proofs.ConstructionAcceptedExecution
