import Goose.Proofs.ConstructionAcceptedEarlierCallLocalGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def callLocalCycleSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def callLocalCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, callLocalCycleSummary⟩
private def callLocalCycleHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [.letS 0 (.call 1 [] 0) 0] (some (.read (.var 0))), callLocalCycleSummary⟩
private def callLocalCycleModule : Module := ⟨#["local-call-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[callLocalCycleEntry, callLocalCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def callLocalCycleConfig : EvalConfig := ⟨.release, callLocalCycleModule⟩

theorem callLocalCycle_validated : validate callLocalCycleModule = .ok () := by cbv

theorem callLocalCycle_graph : RegisterCallGraphWithCallLocals callLocalCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [callLocalCycleConfig, callLocalCycleModule] at contextAt
    subst context
    simp [callLocalCycleConfig, callLocalCycleModule] at implementationAt
    subst implementation
    simp [callLocalCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [callLocalCycleConfig, callLocalCycleModule] at contextAt
      subst context
      simp [callLocalCycleConfig, callLocalCycleModule] at implementationAt
      subst implementation
      apply Or.inr
      refine ⟨_, 0, 0, 1, 0, 0, [], .read (.var 0), ⟨1, "cycle", [], [[]], []⟩,
        callLocalCycleHelper, rfl, rfl, .nil, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · repeat constructor
      · intro descriptor found
        simp [callLocalCycleHelper] at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      · intro id expression origin member
        cases member
    | succ target => simp [callLocalCycleConfig, callLocalCycleModule] at contextAt

private def callLocalCycleStops : Bool :=
  match runModule 20 callLocalCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem callLocalCycle_timeout : callLocalCycleStops = true := by decide +kernel

theorem callLocalCycle_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld callLocalCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel callLocalCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel callLocalCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config := callLocalCycleConfig
  let accepted := acceptedModule config callLocalCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  have initial : InitialGlobalsOutcome fuel config := by
    obtain ⟨completed, types, live, ambient, extend, lower, upper, world, final⟩ :=
      initGlobals_registerCall_fromEvaluation fuel 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
        descriptor 1 0 context callLocalCycleHelper (initial_acceptedWorld config callLocalCycle_validated)
        (futureGlobalsClear_initial config) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) (by rfl) (by rfl) (by rfl) (by
          intro names roots typingAfter rootsAfter
          dsimp only
          intro activeWorld frameSource checked
          let frame := scalarGlobalInitializerFrame config 0 ExecutionState.initial.nextAct names
          let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
          cases fuel with
          | zero =>
            simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
            exact ⟨_, _, _, (fun _ _ found => found), activeWorld, frameSource.futureGlobals, trivial⟩
          | succ fuel =>
            obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, observed, result⟩ :=
              invokeCall_recursive_register_callLocal_earlier fuel config accepted (.int .i64) (Or.inl ⟨.i64, rfl⟩)
                callLocalCycle_graph frame activated [] (declaredRootTypes config.module) (fun _ => False) [] []
                1 context callLocalCycleHelper 0 activeWorld frameSource (by rfl) (by rfl) (by rfl) (by rfl)
                roots typingAfter rootsAfter checked
            have safe : ∃ nextTypes nextLive nextAmbient,
                let outcome := invokeCall fuel config frame.interpretation.environment 1 [] [.register (.int .i64)] 0 activated
                RootTypesExtend (declaredRootTypes config.module) nextTypes ∧ activated.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
                activated.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
                AcceptedWorld config 0 (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive [] [] ∧
                FutureGlobalsClear config 0 (Goose.Proofs.Exit.stepState outcome) ∧
                (match outcome with
                 | .ok carriers _ => nextAmbient = [] ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int .i64) value
                 | .stop .. => True | .escape .. | .jump .. => False) :=
              ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
            obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, clear, result⟩ :=
              evalValue_registerCall_fromInvoke fuel config 0 frame.interpretation.environment activated [] (declaredRootTypes config.module)
                [] [] 1 context callLocalCycleHelper (.int .i64) 0 (by rfl) (by rfl) (by rfl) safe
            exact ⟨nextTypes, nextLive, nextAmbient, extend, world, clear, result⟩)
    have size : config.module.globals.size = 1 := rfl
    have range : List.range config.module.globals.size = [0] := by rfl
    refine ⟨completed, types, live, ambient, [], by omega, ?_, ?_⟩
    · simpa only [range] using world
    · cases run : initGlobals fuel config [0] .initial with
      | ok value after =>
        simp only [run, Goose.Proofs.Exit.stepState] at final
        simp only [range, run, Goose.Proofs.Exit.stepState]
        exact ⟨final.1, by simpa [config, callLocalCycleConfig, callLocalCycleModule] using final.2.1, trivial,
          by simpa [config, callLocalCycleConfig, callLocalCycleModule] using final.2.2⟩
      | stop reason after =>
        simp only [run, Goose.Proofs.Exit.stepState] at final
        simp only [range, run, Goose.Proofs.Exit.stepState]
        exact ⟨by rw [final.1, size]; decide, by simp [runModule, range, run, bind]⟩
      | escape address carriers after | jump destination kind after => simp only [run] at final
  apply acceptedModuleFromGlobals_allFuel fuel config accepted ⟨0, "entry", [], [], []⟩ callLocalCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · simp [callLocalCycleEntry, Block.stmts]
  · rfl

#print axioms callLocalCycle_allFuel
#print axioms callLocalCycle_timeout
#print axioms callLocalCycle_graph
#print axioms callLocalCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
