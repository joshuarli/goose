import Goose.Proofs.ConstructionGhostGlobalStep
import Goose.Proofs.ConstructionInitializerLoopReplay
import Goose.Proofs.ConstructionGhostInvocation
import Goose.Proofs.ConstructionGhostMaterialization

namespace Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Construct Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostMaterialization

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

def nonfixedGlobalContinuation (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (descriptor : Global) (act : Goose.Core.ActId) (materialized : Option (Array Value)) : EvalM Unit := do
  let carrier ← match materialized with
    | some values => do
        let destination ← materializedDestination fuel config.layout act descriptor.ty descriptor.org values.size (.fixed values)
        publishCarriers descriptor.org [.completed destination]
        pure (.completed destination)
    | none =>
        constructLocal ⟨config.module, #[]⟩ act descriptor.ty descriptor.org descriptor.init
          (fun destination => buildExpr fuel config ⟨0, act, #[], [], []⟩ destination descriptor.init)
  let value ← carrierValue carrier
  bindRoot (.global global) value

def globalAfterMaterialization (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (descriptor : Global) (act : Goose.Core.ActId) (result : ExecutionStep (Option (Array Value))) : ExecutionStep Unit :=
  match result with
  | .ok values state => nonfixedGlobalContinuation fuel config global descriptor act values state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem materializedGlobal_initializer_ghost (fuel : Nat) (config : EvalConfig) (path : List Nat)
    (global : Goose.Core.GlobalId) (before : ExecutionState) (descriptor : Global) (count : Nat)
    (found : config.module.globals[global]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count) :
    let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
    let ready := { before with nextAct := before.nextAct + 1 }
    EvaluationTree config environment fuel (path ++ [0]) descriptor.init ready
      (evalValue fuel config environment descriptor.init ready) ∧
    globalInitializer fuel config global before =
      globalAfterMaterialization fuel config global descriptor before.nextAct
        (materializationContinuation (evalValue fuel config environment descriptor.init ready)) := by
  dsimp only
  obtain ⟨tree, execution⟩ := materializeProducer_source_ghost fuel config ⟨0, before.nextAct, #[], [], []⟩
    path descriptor.init { before with nextAct := before.nextAct + 1 } count materialized
  refine ⟨tree, ?_⟩
  simp only [globalInitializer, found, bind, freshAct, EvalM.get, EvalM.set, pure, nonfixed, ↓reduceIte]
  rw [execution]
  simp only [globalAfterMaterialization, nonfixedGlobalContinuation, bind, pure]
  cases materializationContinuation (evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ descriptor.init
    { before with nextAct := before.nextAct + 1 }) <;> rfl

def MaterializedGlobalForest (fuel : Nat) (config : EvalConfig)
    (visits : List (Invocation Goose.Core.GlobalId Unit)) : Prop :=
  ∀ visit ∈ visits, ∀ descriptor count,
    config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    EvaluationTree config environment fuel [visit.ordinal, 0] descriptor.init ready
      (evalValue fuel config environment descriptor.init ready) ∧
    visit.outcome = globalAfterMaterialization fuel config visit.operand descriptor visit.before.nextAct
      (materializationContinuation (evalValue fuel config environment descriptor.init ready))

theorem globalReplay_materializedForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits) :
    MaterializedGlobalForest fuel config visits := by
  intro visit member descriptor count found nonfixed materialized
  obtain ⟨tree, execution⟩ := materializedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand
    visit.before descriptor count found nonfixed materialized
  exact ⟨tree, (visit_executes replay visit member).symm.trans execution⟩

#print axioms materializedGlobal_initializer_ghost
#print axioms globalReplay_materializedForest
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

theorem runModule_globalForests (fuel : Nat) (config : EvalConfig) (before : ExecutionState) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedGlobalForest fuel config visits ∧ MaterializedGlobalForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) := by
  obtain ⟨outcome, visits, replay, fixed, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  exact ⟨outcome, visits, replay, fixed, globalReplay_materializedForest replay, ordered, once, execution⟩

#print axioms runModule_globalForests
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

private def materializedWitnessModule : Module :=
  ⟨#[], #[], #[⟨"value", .varr (.int .i64), .immutable,
    .blockE (.mk 0 [.print [.text "once"] 0]
      (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0, 0⟩],
    #[⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩], #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩

theorem materializedGlobalWitness :
    ∃ state, runModule 100 ⟨.release, materializedWitnessModule⟩ .initial = .ok () state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (runModule 100 ⟨.release, materializedWitnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold stepState materializedWitnessModule <;> cbv

#print axioms materializedGlobalWitness
#print axioms globalReplayWitness
#print axioms runModule_globalReplay
#print axioms fixedGlobal_initializer_ghost
#print axioms initGlobals_forIn
#print axioms initGlobals_replay
end Goose.Proofs.ConstructionGhostGlobalReplay
