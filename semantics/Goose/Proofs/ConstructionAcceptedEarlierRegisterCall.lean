import Goose.Proofs.ConstructionAcceptedEarlierCallTail
import Goose.Proofs.ConstructionAcceptedRegisterCallCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem enterActivation_register_compose_earlier (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier : Nat) (context : Context) (implementation : Impl) (pre : List (Nat × Value)) (ty : Ty) (origin : Nat)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (bodySafe :
      let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
      let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      ∃ nextTypes nextLive nextAmbient,
        let outcome := execActivationBody fuel config activation pre implementation.body pushed
        RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
             ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    ∃ nextTypes nextLive nextAmbient,
      let outcome := (do let carriers ← enterActivation (fuel + 1) config activation pre implementation.body origin
                         deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let outer := (enterActivation (fuel + 1) config activation pre implementation.body origin >>= fun carriers =>
    deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed
  change ∃ nextTypes nextLive nextAmbient, let outcome := outer; _
  change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody fuel config activation pre implementation.body pushed; _ at bodySafe
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, bodyWorld, bodyClear, bodyObserved, bodyResult⟩ := bodySafe
  have pushedObserved : EarlierCallerObservations frontier state pushed types types := by
    intro root earlier
    exact ⟨rfl, rfl, rfl⟩
  have calleeAt : config.module.impls[activation.implementation]? = some implementation := by
    simpa [activation] using implementationAt
  cases execution : execActivationBody fuel config activation pre implementation.body pushed with
  | stop reason after =>
    simp only [activation, pushed] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyObserved bodyResult
    have entered : enterActivation (fuel + 1) config activation pre implementation.body origin pushed = .stop reason after := by
      simp [enterActivation, calleeAt, finishActivation, activation, pushed, execution]
    have outerRun : outer = .stop reason after := by
      dsimp only [outer]
      simp only [bind, entered]
    dsimp only [outer, activation, pushed] at outerRun
    simp only [outerRun, Goose.Proofs.Exit.stepState]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, bodyWorld, bodyClear,
      pushedObserved.trans (Nat.le_refl _) bodyObserved, trivial⟩
  | escape address carriers after | jump destination kind after =>
    simp only [activation, pushed] at execution
    simp [execution] at bodyResult
  | ok carriers after =>
    simp only [activation, pushed] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes bodyWorld bodyClear bodyObserved bodyResult
    obtain ⟨rfl, value, rfl, represented⟩ := bodyResult
    have finished := finishActivation_register_normal config initialized activation ambient nextTypes nextLive regions pending
      ty origin (execActivationBody fuel config activation pre implementation.body) pushed after value
      rfl execution bodyWorld bodyClear
    obtain ⟨finishedRun, finishedWorld, finishedClear⟩ := finished
    have entered : enterActivation (fuel + 1) config activation pre implementation.body origin pushed =
        .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
      simpa [enterActivation, calleeAt, results] using finishedRun
    have outerRun : outer = .ok [.register value]
        { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
      dsimp only [outer]
      simpa only [bind, entered] using deliverCarriers_register (fuel + 1) config.layout ty value origin
        { after with activations := after.activations.filter (fun current => current.act != activation.act) }
    dsimp only [outer, activation, pushed] at outerRun
    simp only [outerRun, Goose.Proofs.Exit.stepState]
    exact ⟨nextTypes, nextLive, ambient, extend, Nat.le_trans (Nat.le_succ _) acts, scopes, finishedWorld, finishedClear,
      (pushedObserved.trans (Nat.le_refl _) bodyObserved).trans (Nat.le_refl _)
        (EarlierCallerObservations.finishActivation frontier activation after nextTypes), rfl, value, rfl, represented⟩

theorem invokeCall_register_compose_earlier (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
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
        EarlierCallerObservations frontier pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
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
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  have transition := invokeCall_zeroArgument_register_transition fuel config environment target context
    implementation ty origin state contextAt implementationAt parameters results
  by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth
  · simp only [depth, ↓reduceIte] at transition
    rw [transition]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear, EarlierCallerObservations.refl frontier state types, trivial⟩
  · have composed := enterActivation_register_compose_earlier fuel config initialized state ambient types regions pending frontier context
      implementation [] ty origin implementationAt results bodySafe
    simp only [depth, ↓reduceIte] at transition
    simp only [transition]
    exact composed

#print axioms enterActivation_register_compose_earlier
#print axioms invokeCall_register_compose_earlier
end Goose.Proofs.ConstructionAcceptedExecution
