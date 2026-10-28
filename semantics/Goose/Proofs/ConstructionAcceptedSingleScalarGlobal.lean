import Goose.Proofs.ConstructionAcceptedScalarGlobalEvaluation
import Goose.Proofs.ConstructionAcceptedInitialGlobalsOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem singleScalarInitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (evaluate : ∀ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame config 0 ExecutionState.initial.nextAct names
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      AcceptedWorld config 0 activated [] (declaredRootTypes config.module) (fun _ => False) [] [] →
      AcceptedFrame config accepted frame activated (declaredRootTypes config.module) →
      CheckedValue frame descriptor.init descriptor.ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := evalValue fuel config frame.interpretation.environment descriptor.init activated
        RootTypesExtend (declaredRootTypes config.module) nextTypes ∧
        AcceptedWorld config 0 (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive [] [] ∧
        FutureGlobalsClear config 0 (Goose.Proofs.Exit.stepState outcome) ∧
        (match outcome with
         | .ok value _ => nextAmbient = [] ∧ ValueRepresentation descriptor.ty value
         | .stop .. => True | .escape .. | .jump .. => False)) : InitialGlobalsOutcome fuel config := by
  obtain ⟨completed, types, live, ambient, extend, lower, upper, world, final⟩ :=
    initGlobals_scalar_fromEvaluation fuel 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
      descriptor (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config) present scalar evaluate
  have range : List.range config.module.globals.size = [0] := by simp [size]
  refine ⟨completed, types, live, ambient, [], by omega, ?_, ?_⟩
  · simpa only [range] using world
  · cases run : initGlobals fuel config [0] .initial with
    | ok value after =>
      simp only [run, Goose.Proofs.Exit.stepState] at final
      simp only [range, run, Goose.Proofs.Exit.stepState]
      exact ⟨final.1, by simpa [size] using final.2.1, trivial, by simpa [size] using final.2.2⟩
    | stop reason after =>
      simp only [run, Goose.Proofs.Exit.stepState] at final
      simp only [range, run, Goose.Proofs.Exit.stepState]
      exact ⟨by omega, by simp [runModule, range, run, bind]⟩
    | escape address carriers after | jump destination kind after => simp only [run] at final

#print axioms singleScalarInitialGlobalsOutcome
end Goose.Proofs.ConstructionAcceptedExecution
