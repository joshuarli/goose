import Goose.Proofs.ConstructionActivationCounterEvaluation
import Goose.Proofs.ConstructionActivationCounterGlobals
import Goose.Proofs.ConstructionGhostCallActivation

namespace Goose.Proofs.ConstructionActivationCounterTheorem
open Goose.Construct Goose.Proofs.ConstructionActivationCounter
open Goose.Proofs.ConstructionActivationCounterEvaluation Goose.Proofs.ConstructionActivationCounterGlobals
open Goose.Proofs.ConstructionGhostGlobalReplay

theorem initGlobals_counter (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    PreservesActivationCounter (initGlobals fuel config globals) :=
  counter_globals fuel config globals (evaluation_preservesActivationCounter fuel config)

theorem afterGlobals_counter (fuel : Nat) (config : EvalConfig) :
    PreservesActivationCounter (afterGlobals fuel config) := by
  unfold afterGlobals
  apply counter_bind
  · exact counter_stateQuery _ (Goose.Proofs.ExitExecution.stateQuery_getImplementation _ _)
  · intro result
    rcases result with ⟨id, implementation⟩
    apply counter_bind
    · exact counter_channelsFor _ _ _ _
    · intro channels
      apply counter_bind
      · exact (evaluation_preservesActivationCounter fuel config).call _ _ _ _ _
      · intro carriers
        exact counter_publishCarriers _ _

theorem runModule_counter (fuel : Nat) (config : EvalConfig) :
    PreservesActivationCounter (runModule fuel config) := by
  apply counter_runModule
  · intro global
    exact counter_globalInitializer fuel config global (evaluation_preservesActivationCounter fuel config)
  · exact afterGlobals_counter fuel config

theorem runModule_nextAct_monotone (fuel : Nat) (config : EvalConfig) (before : ExecutionState) :
    before.nextAct ≤ (Goose.Proofs.Exit.stepState (runModule fuel config before)).nextAct :=
  runModule_counter fuel config before

theorem freshActs_distinct_acrossCall (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before afterFirst afterCall afterSecond : ExecutionState) (first second : Goose.Core.ActId) (carriers : List Carrier)
    (firstStep : freshAct before = .ok first afterFirst)
    (call : invokeCall fuel config environment context arguments channels origin afterFirst = .ok carriers afterCall)
    (secondStep : freshAct afterCall = .ok second afterSecond) : first < second :=
  freshActs_distinct_across _ (evaluation_preservesActivationCounter fuel config |>.call environment context arguments channels origin)
    before afterFirst afterCall afterSecond first second carriers firstStep call secondStep

theorem freshAct_bind_strict (next : Goose.Core.ActId → EvalM α)
    (preserved : ∀ act, PreservesActivationCounter (next act)) (before : ExecutionState) :
    before.nextAct < (Goose.Proofs.Exit.stepState ((freshAct >>= next) before)).nextAct := by
  have after := preserved before.nextAct { before with nextAct := before.nextAct + 1 }
  simp only [freshAct, EvalM.get, EvalM.set, bind, pure]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) after

#print axioms freshAct_bind_strict
#print axioms initGlobals_counter
#print axioms runModule_nextAct_monotone
#print axioms freshActs_distinct_acrossCall
end Goose.Proofs.ConstructionActivationCounterTheorem
