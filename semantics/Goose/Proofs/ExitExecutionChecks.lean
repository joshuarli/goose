import Goose.Construct.Validate
import Goose.Proofs.ExitExecution

set_option Elab.async false

namespace Goose.Proofs.ExitExecutionChecks
open Goose.Construct

def array : Ty := .varr (.int .u8)

def recursiveDestinations : Module :=
  ⟨#["exit-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", array, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .print [.view (.of (.var 0))] 0] none,
      .known ⟨[], [], [], [], [], [], [], [], true, true⟩⟩,
      ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩],
        #[⟨"depth", .int .i64, .immutable, 0, 0⟩, ⟨"inner", array, .immutable, 2, 0⟩],
        .mk 0 [.ifS (.cmp .eq (.read (.var 0)) (.lit .i64 0))
          (.mk 1 [.expr (.call 2 [] 0) 0] none)
          (some (.mk 2 [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
            .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none)) 0] none,
        .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩,
      ⟨"helper", #[], #[], #[], .mk 0 [.returnFrom 0 [.bytes array [66] 0] 0] none,
        .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "builder", [], [[]], []⟩,
      ⟨2, "helper", [], [], []⟩], 0, #[⟨0, 17, "call"⟩], #[], #[⟨1, []⟩]⟩

def accepts (module : Module) : Bool :=
  match validate module with | .ok _ => true | .error _ => false

theorem recursiveDestinations_validated : accepts recursiveDestinations = true := by
  cbv

def returnedObservation : ExecutionResult → Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .done .returned stdout events => some (stdout.data.toList, events)
  | _ => none

set_option maxRecDepth 2048 in
theorem recursiveDestinations_execution :
    returnedObservation (eval 200 .release recursiveDestinations) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]) := by
  cbv

def timeoutActivations : ExecutionStep α → Option (List Goose.Core.ActId × Nat)
  | .stop .timeout state => some (state.activations.map (·.act), state.nextAct)
  | _ => none

def selectedActivation : ExecutionStep RuntimeActivation → Option Goose.Core.ActId
  | .ok activation _ => some activation.act
  | _ => none

theorem recursive_live_activations :
    timeoutActivations (runModule 28 ⟨.release, recursiveDestinations⟩ .initial) =
      some ([3, 2, 1, 0], 4) := by cbv

theorem recursive_live_activations_fresh :
    Goose.Proofs.ExitExecution.FreshActivations
      (Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)) :=
  Goose.Proofs.ExitExecution.runModule_freshActivations _ _

set_option maxRecDepth 2048 in
theorem recursive_live_nearest_target :
    selectedActivation (targetActivation ⟨.release, recursiveDestinations⟩ 0
      (Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial))) = some 2 := by
  cbv

def overlappingTargets : Module :=
  ⟨#["overlapping-targets.goose"], #[.int .i64], #[],
    #[⟨"entry", #[], #[], #[⟨"result", .int .i64, .immutable, 0, 0⟩],
        .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.expr (.read (.var 0))] 0] none,
        .known ⟨[], [], [], [], [], [], [], [], false, true⟩⟩,
      ⟨"member", #[], #[⟨.int .i64, .register, none⟩], #[],
        .mk 0 [.expr (.call 2 [] 0) 0] (some (.lit .i64 999)),
        .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩,
      ⟨"escape", #[], #[], #[], .mk 0 [.returnFrom 1 [.lit .i64 7] 0] none,
        .known ⟨[], [], [], [], [], [], [1], [1], false, false⟩⟩,
      ⟨"other", #[], #[⟨.int .i64, .register, none⟩], #[],
        .mk 0 [] (some (.lit .i64 9)),
        .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "member", [], [[]], []⟩,
      ⟨2, "escape", [], [], []⟩, ⟨3, "other", [], [[]], []⟩], 0,
    #[⟨0, 17, "let"⟩], #[], #[⟨1, []⟩, ⟨1, [3]⟩]⟩

theorem overlappingTargets_validated : accepts overlappingTargets = true := by cbv

theorem overlappingTargets_execution :
    returnedObservation (eval 100 .release overlappingTargets) = some ([55, 10], []) := by cbv

def overlapReachable : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 15 ⟨.release, overlappingTargets⟩ .initial)

def overlapExit : ExecutionStep Flow :=
  match overlapReachable.activations.head? with
  | some source => execStmt 100 ⟨.release, overlappingTargets⟩ source
      (.returnFrom 1 [.lit .i64 7] 0) overlapReachable
  | none => .stop (.fault .unbound) overlapReachable

def exitObservation : ExecutionStep α → Option (ExitAddress × List Carrier)
  | .escape address carriers _ => some (address, carriers)
  | _ => none

theorem overlappingTargets_live_stack :
    timeoutActivations (runModule 15 ⟨.release, overlappingTargets⟩ .initial) =
      some ([2, 1, 0], 3) := by cbv

theorem overlappingTargets_reachable_address :
    exitObservation overlapExit = some (⟨1, .nonlocal 1⟩, [.register (.int .i64 7)]) := by cbv

def inactiveTarget : Module := { overlappingTargets with
  impls := overlappingTargets.impls.mapIdx fun index implementation =>
    if index == 0 then { implementation with vars := #[], body := .mk 0 [.expr (.call 2 [] 0) 0] none }
    else implementation }

theorem inactiveTarget_rejected :
    validate inactiveTarget = .error ⟨.summary, "V-SUMMARY: missing required nonlocal target"⟩ := by cbv

#print axioms recursiveDestinations_validated
#print axioms recursiveDestinations_execution
#print axioms recursive_live_activations
#print axioms recursive_live_activations_fresh
#print axioms recursive_live_nearest_target
#print axioms overlappingTargets_validated
#print axioms overlappingTargets_execution
#print axioms overlappingTargets_live_stack
#print axioms overlappingTargets_reachable_address
#print axioms inactiveTarget_rejected
#print axioms Goose.Proofs.ExitExecution.preservesFresh_copyValue
#print axioms Goose.Proofs.ExitExecution.preservesFresh_deliverCarriers
#print axioms Goose.Proofs.ExitExecution.preservesFresh_truncateOwner
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendFixedValues
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendRun
#print axioms Goose.Proofs.ExitExecution.evaluation_preservesFresh
#print axioms Goose.Proofs.ExitExecution.initGlobals_preservesFresh
#print axioms Goose.Proofs.ExitExecution.runModule_freshActivations
#print axioms Goose.Proofs.ExitExecution.targetActivation_selects_nearest
#print axioms Goose.Proofs.ExitExecution.runModule_selectedTarget_nearest

end Goose.Proofs.ExitExecutionChecks
