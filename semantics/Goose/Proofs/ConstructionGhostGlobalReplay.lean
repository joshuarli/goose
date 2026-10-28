import Goose.Proofs.ConstructionGhostGlobalStep
import Goose.Proofs.ConstructionInitializerLoopReplay
import Goose.Proofs.ConstructionGhostInvocation

namespace Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Construct Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Proofs.ConstructionGhostInvocation

def discardGlobalValues : ExecutionStep (List Unit) → ExecutionStep Unit
  | .ok _ state => .ok () state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem initGlobals_forIn (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (before : ExecutionState) :
    initGlobals fuel config globals before =
      (match (forIn globals PUnit.unit fun global _ => do
        globalInitializer fuel config global
        pure (.yield PUnit.unit)) before with
      | .ok _ state => .ok () state
      | .stop reason state => .stop reason state
      | .escape address carriers state => .escape address carriers state
      | .jump target kind state => .jump target kind state) := by
  induction globals generalizing before with
  | nil => simp [initGlobals, pure]
  | cons global rest ih =>
    rw [initGlobals_step]
    simp only [bind, List.forIn_cons]
    cases head : globalInitializer fuel config global before with
    | ok value middle =>
      cases value
      simp only [head, pure, bind]
      rw [ih middle]
      cases (forIn rest PUnit.unit fun global _ => do
        globalInitializer fuel config global
        pure (.yield PUnit.unit)) middle <;> rfl
    | stop reason after | escape address carriers after | jump target kind after => simp [head]

theorem initGlobals_replay (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (before : ExecutionState) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 globals [] before outcome visits ∧
      visits.map Invocation.operand = globals.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      initGlobals fuel config globals before = discardGlobalValues outcome := by
  obtain ⟨outcome, visits, replay, loop, ordered, once⟩ :=
    initializerLoop_replay (globalInitializer fuel config) globals before
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  rw [initGlobals_forIn, loop]
  cases outcome <;> rfl

def globalAfterValue (global : Goose.Core.GlobalId) (value : ExecutionStep Value) : ExecutionStep Unit :=
  match value with
  | .ok value state => bindRoot (.global global) value state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem fixedGlobal_initializer_ghost (fuel : Nat) (config : EvalConfig) (path : List Nat)
    (global : Goose.Core.GlobalId) (before : ExecutionState) (descriptor : Global)
    (found : config.module.globals[global]? = some descriptor) (fixed : descriptor.ty.nonfixed = false) :
    let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
    let ready := { before with nextAct := before.nextAct + 1 }
    EvaluationTree config environment fuel (path ++ [0]) descriptor.init ready
      (evalValue fuel config environment descriptor.init ready) ∧
    globalInitializer fuel config global before =
      globalAfterValue global (evalValue fuel config environment descriptor.init ready) := by
  dsimp only
  refine ⟨evaluationTree_exists fuel config _ _ _ _, ?_⟩
  simp only [globalInitializer, found, bind, freshAct, EvalM.get, EvalM.set, pure, fixed, Bool.false_eq_true,
    ↓reduceIte, globalAfterValue]
  cases evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ descriptor.init
    { before with nextAct := before.nextAct + 1 } <;> rfl

def FixedGlobalForest (fuel : Nat) (config : EvalConfig)
    (visits : List (Invocation Goose.Core.GlobalId Unit)) : Prop :=
  ∀ visit ∈ visits, ∀ descriptor,
    config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = false →
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    EvaluationTree config environment fuel [visit.ordinal, 0] descriptor.init ready
      (evalValue fuel config environment descriptor.init ready) ∧
    visit.outcome = globalAfterValue visit.operand (evalValue fuel config environment descriptor.init ready)

theorem globalReplay_fixedForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits) :
    FixedGlobalForest fuel config visits := by
  intro visit member descriptor found fixed
  obtain ⟨tree, execution⟩ := fixedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand visit.before descriptor found fixed
  refine ⟨tree, ?_⟩
  exact (visit_executes replay visit member).symm.trans execution

def afterGlobals (fuel : Nat) (config : EvalConfig) : EvalM Unit := do
  let (_, implementation) ← getImplementation config config.module.entry
  let channels ← channelsFor config.layout 0 implementation.results.toList 0
  let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
  let carriers ← invokeCall fuel config environment config.module.entry [] channels 0
  publishCarriers 0 carriers

def moduleAfterGlobals (fuel : Nat) (config : EvalConfig) (globals : ExecutionStep Unit) : ExecutionStep Unit :=
  match globals with
  | .ok () state => afterGlobals fuel config state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem runModule_globalReplay (fuel : Nat) (config : EvalConfig) (before : ExecutionState) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedGlobalForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    initGlobals_replay fuel config (List.range config.module.globals.size) before
  refine ⟨outcome, visits, replay, globalReplay_fixedForest replay, ordered, once, ?_⟩
  simp only [runModule, bind, execution, moduleAfterGlobals, afterGlobals]
  cases outcome <;> rfl

private def witnessModule : Module :=
  ⟨#[], #[], #[⟨"first", .int .i64, .immutable,
    .blockE (.mk 0 [.print [.text "first"] 0] (some (.lit .i64 7))) 0, 0⟩,
    ⟨"second", .int .i64, .immutable,
    .blockE (.mk 1 [.print [.text "second"] 0] (some (.lit .i64 8))) 0, 0⟩],
    #[⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩], #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem globalReplayWitness :
    ∃ state, runModule 100 ⟨.release, witnessModule⟩ .initial = .ok () state ∧
      state.construction.stdout.data.toList =
        [102, 105, 114, 115, 116, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨stepState (runModule 100 ⟨.release, witnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold stepState witnessModule <;> cbv

#print axioms globalReplayWitness
#print axioms runModule_globalReplay
#print axioms fixedGlobal_initializer_ghost
#print axioms initGlobals_forIn
#print axioms initGlobals_replay
end Goose.Proofs.ConstructionGhostGlobalReplay
