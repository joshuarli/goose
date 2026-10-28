import Goose.Proofs.ConstructionAcceptedSingleArgumentTransition
import Goose.Proofs.ConstructionAcceptedEarlierRegisterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_singleArgument_register_compose (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (state argumentState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier target : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Arg) (value : Value)
    (ty : Ty) (origin : Nat)
    (world : AcceptedWorld config initialized argumentState ambient types live regions pending)
    (clear : FutureGlobalsClear config initialized argumentState)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (evaluated : evalArguments (fuel + 1) config environment implementation.vars [parameter] [argument] state = .ok [value] argumentState)
    (bodySafe :
      let activation : RuntimeActivation := ⟨context.impl, argumentState.nextAct, implementation.vars, [], [.register ty]⟩
      let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
      ∃ nextTypes nextLive nextAmbient,
        let outcome := execActivationBody fuel config activation [(parameter.var, value)] implementation.body pushed
        RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
             ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall (fuel + 2) config environment target [argument] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ argumentState.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      argumentState.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier argumentState (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  have transition := invokeCall_singleArgument_register_transition fuel config environment target context implementation parameter argument
    ty origin state argumentState value contextAt implementationAt parameters results evaluated
  by_cases depth : argumentState.activations.length ≥ Goose.Core.maxCallDepth
  · simp only [depth, ↓reduceIte] at transition
    rw [transition]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, clear,
      EarlierCallerObservations.refl frontier argumentState types, trivial⟩
  · have composed := enterActivation_register_compose_earlier fuel config initialized argumentState ambient types regions pending frontier context
      implementation [(parameter.var, value)] ty origin implementationAt results bodySafe
    simp only [depth, ↓reduceIte] at transition
    simp only [transition]
    exact composed

#print axioms invokeCall_singleArgument_register_compose
end Goose.Proofs.ConstructionAcceptedExecution
