import Goose.Proofs.ConstructionGhostSourceFuel
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostMaterialization

def FixedSourceForest (fuel : Nat) (config : EvalConfig)
    (visits : List (Invocation Goose.Core.GlobalId Unit)) : Prop :=
  ∀ visit ∈ visits, ∀ descriptor,
    config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = false →
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    SourceHistory config fuel [visit.ordinal, 0] (.value environment descriptor.init) ready
      (evalValue fuel config environment descriptor.init ready) ∧
    visit.outcome = globalAfterValue visit.operand (evalValue fuel config environment descriptor.init ready)

theorem globalReplay_fuelSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, FuelSupport config fuel (.value environment descriptor.init)) :
    FixedSourceForest fuel config visits := by
  intro visit member descriptor found fixed
  dsimp only
  refine ⟨fuelHistory_exists fuel config _ _ _ (supported visit.operand descriptor found fixed _), ?_⟩
  obtain ⟨tree, execution⟩ := fixedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand visit.before descriptor found fixed
  exact (visit_executes replay visit member).symm.trans execution

theorem globalReplay_sourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    FixedSourceForest fuel config visits := by
  apply globalReplay_fuelSourceForest replay
  intro global descriptor found fixed environment
  exact .legacy fuel (supported global descriptor found fixed environment)

theorem runModule_fixedSourceForest (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) := by
  obtain ⟨outcome, visits, replay, fixed, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  exact ⟨outcome, visits, replay, globalReplay_sourceForest replay supported, ordered, once, execution⟩

def MaterializedSourceForest (fuel : Nat) (config : EvalConfig)
    (visits : List (Invocation Goose.Core.GlobalId Unit)) : Prop :=
  ∀ visit ∈ visits, ∀ descriptor count,
    config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    SourceHistory config fuel [visit.ordinal, 0] (.value environment descriptor.init) ready
      (evalValue fuel config environment descriptor.init ready) ∧
    visit.outcome = globalAfterMaterialization fuel config visit.operand descriptor visit.before.nextAct
      (materializationContinuation (evalValue fuel config environment descriptor.init ready))

theorem globalReplay_materializedFuelSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, FuelSupport config fuel (.value environment descriptor.init)) :
    MaterializedSourceForest fuel config visits := by
  intro visit member descriptor count found nonfixed materialized
  dsimp only
  refine ⟨fuelHistory_exists fuel config _ _ _ (supported visit.operand descriptor count found nonfixed materialized _), ?_⟩
  obtain ⟨tree, execution⟩ := materializedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand
    visit.before descriptor count found nonfixed materialized
  exact (visit_executes replay visit member).symm.trans execution

theorem globalReplay_materializedSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    MaterializedSourceForest fuel config visits := by
  apply globalReplay_materializedFuelSourceForest replay
  intro global descriptor count found nonfixed materialized environment
  exact .legacy fuel (supported global descriptor count found nonfixed materialized environment)

theorem runModule_sourceForests (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (materializedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ :=
    runModule_fixedSourceForest fuel config before fixedSupported
  exact ⟨outcome, visits, replay, forest, globalReplay_materializedSourceForest replay materializedSupported,
    ordered, once, execution⟩

#print axioms globalReplay_materializedSourceForest
#print axioms runModule_sourceForests

def directGlobalAfterBuild (global : Goose.Core.GlobalId) (descriptor : Global) (destination : Goose.Core.DestinationId) :
    ExecutionStep Unit → ExecutionStep Unit
  | .ok () state => (do
      let destination ← completedReceivingDestination destination
      publishCarriers descriptor.org [.completed destination]
      let value ← carrierValue (.completed destination)
      bindRoot (.global global) value) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def directGlobalAfterAllocation (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (descriptor : Global) (act : Goose.Core.ActId) : ExecutionStep Goose.Core.DestinationId → ExecutionStep Unit
  | .ok destination state => directGlobalAfterBuild global descriptor destination
      (buildExpr fuel config ⟨0, act, #[], [], []⟩ destination descriptor.init state)
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem directGlobal_source (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (descriptor : Global) (before : ExecutionState)
    (found : config.module.globals[global]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (direct : ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none) :
    globalInitializer fuel config global before =
      directGlobalAfterAllocation fuel config global descriptor before.nextAct
        (newDestination config.layout before.nextAct descriptor.ty .value descriptor.org none
          (producerCount? ⟨config.module, #[]⟩ descriptor.init) { before with nextAct := before.nextAct + 1 }) := by
  simp only [globalInitializer, found, bind, freshAct, EvalM.get, EvalM.set, pure, nonfixed, ↓reduceIte,
    materializeProducer, direct, constructLocal, directGlobalAfterAllocation, directGlobalAfterBuild]
  cases result : newDestination config.layout before.nextAct descriptor.ty .value descriptor.org none
    (producerCount? ⟨config.module, #[]⟩ descriptor.init) { before with nextAct := before.nextAct + 1 } with
  | ok destination ready =>
      simp only [EvalConfig.layout] at result
      simp only [result, bind, pure, directGlobalAfterBuild]
      cases built : buildExpr fuel config ⟨0, before.nextAct, #[], [], []⟩ destination descriptor.init ready with
      | ok unit after =>
          cases unit
          simp only [built, bind, pure]
          cases completed : completedReceivingDestination destination after with
          | ok current finished =>
              simp only [completed, bind, pure]
              cases published : publishCarriers descriptor.org [.completed current] finished <;>
                simp [published, bind, pure]
          | stop | escape | jump => simp_all [bind, pure]
      | stop | escape | jump => simp_all [bind, pure]
  | stop | escape | jump => simp_all [bind, pure, EvalConfig.layout]

def DirectSourceForest (fuel : Nat) (config : EvalConfig)
    (visits : List (Invocation Goose.Core.GlobalId Unit)) : Prop :=
  ∀ visit ∈ visits, ∀ descriptor,
    config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let allocated := { visit.before with nextAct := visit.before.nextAct + 1 }
    visit.outcome = directGlobalAfterAllocation fuel config visit.operand descriptor visit.before.nextAct
      (newDestination config.layout visit.before.nextAct descriptor.ty .value descriptor.org none
        (producerCount? ⟨config.module, #[]⟩ descriptor.init) allocated) ∧
    ∀ destination ready,
      newDestination config.layout visit.before.nextAct descriptor.ty .value descriptor.org none
        (producerCount? ⟨config.module, #[]⟩ descriptor.init) allocated = .ok destination ready →
      SourceHistory config fuel [visit.ordinal, 0] (.builder environment destination descriptor.init) ready
        (buildExpr fuel config environment destination descriptor.init ready)

theorem globalReplay_directFuelSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, FuelSupport config fuel (.builder environment destination descriptor.init)) :
    DirectSourceForest fuel config visits := by
  intro visit member descriptor found nonfixed direct
  dsimp only
  refine ⟨(visit_executes replay visit member).symm.trans
    (directGlobal_source fuel config visit.operand descriptor visit.before found nonfixed direct), ?_⟩
  intro destination ready allocated
  exact fuelHistory_exists fuel config _ _ _ (supported visit.operand descriptor found nonfixed direct _ destination)

theorem globalReplay_directSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init)) :
    DirectSourceForest fuel config visits := by
  apply globalReplay_directFuelSourceForest replay
  intro global descriptor found nonfixed direct environment destination
  exact .legacy fuel (supported global descriptor found nonfixed direct environment destination)

#print axioms globalReplay_directFuelSourceForest
#print axioms globalReplay_directSourceForest

#print axioms directGlobal_source

def entryCallResult : ExecutionStep (List Carrier) → ExecutionStep Unit
  | .ok carriers state => publishCarriers 0 carriers state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem runModule_fixedGlobalsAndEntry (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (entryContext : Context) (entryImplementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some entryContext)
    (implementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (resultsEmpty : entryImplementation.results = #[])
    (entrySupported : SupportedOperation config (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0)) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ initialized, discardGlobalValues outcome = .ok () initialized →
        SourceHistory config fuel [config.module.globals.size, 0]
          (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) initialized
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) ∧
        runModule fuel config before = entryCallResult
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ :=
    runModule_fixedSourceForest fuel config before supported
  refine ⟨outcome, visits, replay, forest, ordered, once, execution, ?_⟩
  intro initialized globals
  refine ⟨history_exists fuel config _ _ _ entrySupported, ?_⟩
  rw [execution, globals]
  simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, contextFound, implementationFound, resultsEmpty,
    Array.toList_empty, channelsFor, List.mapM_nil, pure, entryCallResult]
  cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized <;> rfl

#print axioms runModule_fixedGlobalsAndEntry

theorem runModule_sourceForestsAndEntry (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (materializedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (entryContext : Context) (entryImplementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some entryContext)
    (implementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (resultsEmpty : entryImplementation.results = #[])
    (entrySupported : SupportedOperation config (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0)) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ initialized, discardGlobalValues outcome = .ok () initialized →
        SourceHistory config fuel [config.module.globals.size, 0]
          (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) initialized
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) ∧
        runModule fuel config before = entryCallResult
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution, entry⟩ :=
    runModule_fixedGlobalsAndEntry fuel config before fixedSupported entryContext entryImplementation
      contextFound implementationFound resultsEmpty entrySupported
  exact ⟨outcome, visits, replay, forest, globalReplay_materializedSourceForest replay materializedSupported,
    ordered, once, execution, entry⟩

#print axioms runModule_sourceForestsAndEntry

theorem runModule_allSourceForestsAndEntry (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (materializedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, SupportedOperation config (.value environment descriptor.init))
    (directSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init))
    (entryContext : Context) (entryImplementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some entryContext)
    (implementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (resultsEmpty : entryImplementation.results = #[])
    (entrySupported : SupportedOperation config (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0)) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧ DirectSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ initialized, discardGlobalValues outcome = .ok () initialized →
        SourceHistory config fuel [config.module.globals.size, 0]
          (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) initialized
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) ∧
        runModule fuel config before = entryCallResult
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, materialized, ordered, once, execution, entry⟩ :=
    runModule_sourceForestsAndEntry fuel config before fixedSupported materializedSupported entryContext entryImplementation
      contextFound implementationFound resultsEmpty entrySupported
  exact ⟨outcome, visits, replay, fixed, materialized, globalReplay_directSourceForest replay directSupported,
    ordered, once, execution, entry⟩

#print axioms runModule_allSourceForestsAndEntry

private def witnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def witnessCallee : Impl := ⟨"source", #[], #[], #[], .mk 1 [.print [.text "x"] 0] none, .unknown⟩
private def witnessCalleeContext : Context := ⟨1, "source", [], [], []⟩
private def witnessGlobal : Global := ⟨"g", .arr .unit 3, .immutable,
  .fill (.arr .unit 3) (.call 1 [] 0) 0, 0⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[witnessGlobal], #[witnessEntry, witnessCallee],
    #[⟨0, "entry", [], [], []⟩, witnessCalleeContext], 0, #[], #[], #[]⟩⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem witness_supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    witnessConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false →
    ∀ environment, SupportedOperation witnessConfig (.value environment descriptor.init) := by
  intro global descriptor found fixed environment
  have descriptorEq : descriptor = witnessGlobal := by
    cases global with
    | zero => simpa [witnessConfig] using found.symm
    | succ global => simp [witnessConfig] at found
  subst descriptor
  have bodySupported : ∀ scopedEnvironment, SupportedOperation witnessConfig
      (.statements scopedEnvironment [.print [.text "x"] 0]) := by
    intro scopedEnvironment
    exact .sequence scopedEnvironment (.printText scopedEnvironment "x" 0) (.empty scopedEnvironment)
  have callee : SupportedOperation witnessConfig (.call environment 1 0) := by
    apply SupportedOperation.call environment 1 0 witnessCalleeContext witnessCallee
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 1 _ 0 bodySupported
  exact .fill environment .unit 3 0 (.call 1 [] 0) rfl
    (.valueCall environment 1 0 witnessCalleeContext witnessCallee rfl rfl rfl callee)

private def witnessEntryContext : Context := ⟨0, "entry", [], [], []⟩

private theorem witness_entrySupported : SupportedOperation witnessConfig (.call ⟨0, 0, #[], [], []⟩ 0 0) := by
  apply SupportedOperation.call ⟨0, 0, #[], [], []⟩ 0 0 witnessEntryContext witnessEntry
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 [] 0 (fun environment => .empty environment)

theorem witness_globalAndEntryHistories (fuel : Nat) : ∃ outcome visits,
    OperandReplay (globalInitializer fuel witnessConfig) 0 (List.range witnessConfig.module.globals.size) [] .initial outcome visits ∧
    FixedSourceForest fuel witnessConfig visits ∧
    ∀ initialized, discardGlobalValues outcome = .ok () initialized →
      SourceHistory witnessConfig fuel [witnessConfig.module.globals.size, 0]
        (.call ⟨0, 0, #[], [], []⟩ 0 0) initialized
        (invokeCall fuel witnessConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
      runModule fuel witnessConfig .initial = entryCallResult
        (invokeCall fuel witnessConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution, entry⟩ :=
    runModule_fixedGlobalsAndEntry fuel witnessConfig .initial witness_supported witnessEntryContext witnessEntry
      rfl rfl rfl witness_entrySupported
  exact ⟨outcome, visits, replay, forest, entry⟩

#print axioms witness_globalAndEntryHistories

theorem witness_globalFillOnce : ∃ outcome visits state,
    OperandReplay (globalInitializer 40 witnessConfig) 0 (List.range witnessConfig.module.globals.size) [] .initial outcome visits ∧
    FixedSourceForest 40 witnessConfig visits ∧
    runModule 40 witnessConfig .initial = .ok () state ∧ state.construction.stdout.data.toList = [120, 10] := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ :=
    runModule_fixedSourceForest 40 witnessConfig .initial witness_supported
  refine ⟨outcome, visits, witnessState (runModule 40 witnessConfig .initial), replay, forest, ?_, ?_⟩ <;>
    unfold witnessState witnessConfig witnessEntry witnessCallee witnessCalleeContext witnessGlobal <;> cbv

private def materializedGlobal : Global := ⟨"g", .varr (.int .i64), .immutable,
  .values [.fill (.arr (.int .i64) 3) (.lit .i64 7) 0], 0⟩
private def materializedConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[materializedGlobal], #[witnessEntry], #[witnessEntryContext], 0, #[], #[], #[]⟩⟩

private theorem materialized_descriptor (global : Goose.Core.GlobalId) (descriptor : Global)
    (found : materializedConfig.module.globals[global]? = some descriptor) : descriptor = materializedGlobal := by
  cases global with
  | zero => simpa [materializedConfig] using found.symm
  | succ global => simp [materializedConfig] at found

private theorem materialized_fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    materializedConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false →
    ∀ environment, SupportedOperation materializedConfig (.value environment descriptor.init) := by
  intro global descriptor found fixed environment
  have descriptorEq := materialized_descriptor global descriptor found
  subst descriptor
  simp [materializedGlobal, Ty.nonfixed] at fixed

private theorem materialized_supported (fuel : Nat) : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
    materializedConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨materializedConfig.module, #[]⟩ descriptor.init = some count →
    ∀ environment, SupportedOperation materializedConfig (.value environment descriptor.init) := by
  intro global descriptor count found nonfixed countFound environment
  have descriptorEq := materialized_descriptor global descriptor found
  subst descriptor
  exact .singleton environment _ (.value environment (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))

private theorem materialized_entrySupported :
    SupportedOperation materializedConfig (.call ⟨0, 0, #[], [], []⟩ 0 0) := by
  apply SupportedOperation.call ⟨0, 0, #[], [], []⟩ 0 0 witnessEntryContext witnessEntry
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 [] 0 (fun environment => .empty environment)

theorem witness_materializedGlobalAndEntry (fuel : Nat) : ∃ outcome visits,
    OperandReplay (globalInitializer fuel materializedConfig) 0 (List.range materializedConfig.module.globals.size) [] .initial outcome visits ∧
    MaterializedSourceForest fuel materializedConfig visits ∧
    ∀ initialized, discardGlobalValues outcome = .ok () initialized →
      SourceHistory materializedConfig fuel [materializedConfig.module.globals.size, 0]
        (.call ⟨0, 0, #[], [], []⟩ 0 0) initialized
        (invokeCall fuel materializedConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
      runModule fuel materializedConfig .initial = entryCallResult
        (invokeCall fuel materializedConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, materialized, ordered, once, execution, entry⟩ :=
    runModule_sourceForestsAndEntry fuel materializedConfig .initial materialized_fixedSupported (materialized_supported fuel)
      witnessEntryContext witnessEntry rfl rfl rfl materialized_entrySupported
  exact ⟨outcome, visits, replay, materialized, entry⟩

#print axioms witness_materializedGlobalAndEntry

theorem witness_materializedGlobal : ∃ outcome visits state,
    ordinaryProducerCount? 40 ⟨materializedConfig.module, #[]⟩ materializedGlobal.init = some 3 ∧
    OperandReplay (globalInitializer 40 materializedConfig) 0 (List.range materializedConfig.module.globals.size) [] .initial outcome visits ∧
    MaterializedSourceForest 40 materializedConfig visits ∧
    runModule 40 materializedConfig .initial = .ok () state := by
  obtain ⟨outcome, visits, replay, fixed, materialized, ordered, once, execution⟩ :=
    runModule_sourceForests 40 materializedConfig .initial materialized_fixedSupported (materialized_supported 40)
  refine ⟨outcome, visits, witnessState (runModule 40 materializedConfig .initial), ?_, replay, materialized, ?_⟩
  · unfold materializedConfig materializedGlobal
    cbv
  · unfold witnessState materializedConfig materializedGlobal witnessEntry witnessEntryContext
    cbv

#print axioms witness_materializedGlobal

private def directGlobal : Global := ⟨"bytes", .varr (.int .u8), .immutable,
  .bytes (.varr (.int .u8)) [65, 66] 0, 0⟩
private def directConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[directGlobal], #[witnessEntry], #[witnessEntryContext], 0, #[], #[], #[]⟩⟩

private theorem direct_descriptor (global : Goose.Core.GlobalId) (descriptor : Global)
    (found : directConfig.module.globals[global]? = some descriptor) : descriptor = directGlobal := by
  cases global with
  | zero => simpa [directConfig] using found.symm
  | succ global => simp [directConfig] at found

private theorem direct_fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    directConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false →
    ∀ environment, SupportedOperation directConfig (.value environment descriptor.init) := by
  intro global descriptor found fixed environment
  have descriptorEq := direct_descriptor global descriptor found
  subst descriptor
  simp [directGlobal, Ty.nonfixed] at fixed

private theorem direct_materializedSupported (fuel : Nat) : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
    directConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨directConfig.module, #[]⟩ descriptor.init = some count →
    ∀ environment, SupportedOperation directConfig (.value environment descriptor.init) := by
  intro global descriptor count found nonfixed countFound environment
  have descriptorEq := direct_descriptor global descriptor found
  subst descriptor
  simp [directGlobal, ordinaryProducerCount?, producerCount?, literalCount] at countFound

private theorem direct_supported (fuel : Nat) : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    directConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨directConfig.module, #[]⟩ descriptor.init = none →
    ∀ environment destination, SupportedOperation directConfig (.builder environment destination descriptor.init) := by
  intro global descriptor found nonfixed direct environment destination
  have descriptorEq := direct_descriptor global descriptor found
  subst descriptor
  exact .builderBytes environment destination (.varr (.int .u8)) [65, 66] 0

private theorem direct_entrySupported : SupportedOperation directConfig (.call ⟨0, 0, #[], [], []⟩ 0 0) := by
  apply SupportedOperation.call ⟨0, 0, #[], [], []⟩ 0 0 witnessEntryContext witnessEntry
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 [] 0 (fun environment => .empty environment)

theorem witness_directGlobal (fuel : Nat) : ∃ outcome visits,
    OperandReplay (globalInitializer fuel directConfig) 0 (List.range directConfig.module.globals.size) [] .initial outcome visits ∧
    DirectSourceForest fuel directConfig visits ∧
    ∀ initialized, discardGlobalValues outcome = .ok () initialized →
      SourceHistory directConfig fuel [directConfig.module.globals.size, 0] (.call ⟨0, 0, #[], [], []⟩ 0 0) initialized
        (invokeCall fuel directConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
      runModule fuel directConfig .initial = entryCallResult
        (invokeCall fuel directConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, materialized, direct, ordered, once, execution, entry⟩ :=
    runModule_allSourceForestsAndEntry fuel directConfig .initial direct_fixedSupported (direct_materializedSupported fuel)
      (direct_supported fuel) witnessEntryContext witnessEntry rfl rfl rfl direct_entrySupported
  exact ⟨outcome, visits, replay, direct, entry⟩

theorem witness_directGlobal_events : ∃ state,
    runModule 40 directConfig .initial = .ok () state ∧
    state.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  refine ⟨witnessState (runModule 40 directConfig .initial), ?_, ?_⟩ <;>
    unfold witnessState directConfig directGlobal witnessEntry witnessEntryContext <;> cbv

private def nestedGlobalOperand : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def nestedGlobal : Global := ⟨"nested", .varr (.varr (.int .u8)), .immutable,
  .arrLit (.varr (.varr (.int .u8))) [nestedGlobalOperand, nestedGlobalOperand] 0, 0⟩
private def nestedConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[nestedGlobal], #[witnessEntry], #[witnessEntryContext], 0, #[], #[], #[]⟩⟩

private theorem nested_descriptor (global : Goose.Core.GlobalId) (descriptor : Global)
    (found : nestedConfig.module.globals[global]? = some descriptor) : descriptor = nestedGlobal := by
  cases global with
  | zero => simpa [nestedConfig] using found.symm
  | succ global => simp [nestedConfig] at found

private theorem nested_fixedSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    nestedConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false →
    ∀ environment, SupportedOperation nestedConfig (.value environment descriptor.init) := by
  intro global descriptor found fixed environment
  have descriptorEq := nested_descriptor global descriptor found
  subst descriptor
  simp [nestedGlobal, Ty.nonfixed] at fixed

private theorem nested_materializedSupported (fuel : Nat) : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
    nestedConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨nestedConfig.module, #[]⟩ descriptor.init = some count →
    ∀ environment, SupportedOperation nestedConfig (.value environment descriptor.init) := by
  intro global descriptor count found nonfixed countFound environment
  have descriptorEq := nested_descriptor global descriptor found
  subst descriptor
  simp [nestedGlobal, ordinaryProducerCount?, producerCount?, literalCount] at countFound

private theorem nested_directSupported (fuel : Nat) : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
    nestedConfig.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨nestedConfig.module, #[]⟩ descriptor.init = none →
    ∀ environment destination, SupportedOperation nestedConfig (.builder environment destination descriptor.init) := by
  intro global descriptor found nonfixed direct environment destination
  have descriptorEq := nested_descriptor global descriptor found
  subst descriptor
  unfold nestedGlobal
  apply SupportedOperation.builderArray
  intro operand member current element
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals exact byteElement_supported nestedConfig environment current element (.varr (.int .u8)) [65, 66] 0

private theorem nested_entrySupported : SupportedOperation nestedConfig (.call ⟨0, 0, #[], [], []⟩ 0 0) := by
  apply SupportedOperation.call ⟨0, 0, #[], [], []⟩ 0 0 witnessEntryContext witnessEntry
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 [] 0 (fun environment => .empty environment)

theorem witness_nestedGlobal (fuel : Nat) : ∃ outcome visits,
    OperandReplay (globalInitializer fuel nestedConfig) 0 (List.range nestedConfig.module.globals.size) [] .initial outcome visits ∧
    DirectSourceForest fuel nestedConfig visits ∧
    ∀ initialized, discardGlobalValues outcome = .ok () initialized →
      SourceHistory nestedConfig fuel [nestedConfig.module.globals.size, 0] (.call ⟨0, 0, #[], [], []⟩ 0 0) initialized
        (invokeCall fuel nestedConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
      runModule fuel nestedConfig .initial = entryCallResult
        (invokeCall fuel nestedConfig ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, materialized, direct, ordered, once, execution, entry⟩ :=
    runModule_allSourceForestsAndEntry fuel nestedConfig .initial nested_fixedSupported (nested_materializedSupported fuel)
      (nested_directSupported fuel) witnessEntryContext witnessEntry rfl rfl rfl nested_entrySupported
  exact ⟨outcome, visits, replay, direct, entry⟩

theorem witness_nestedGlobal_events : ∃ state,
    runModule 40 nestedConfig .initial = .ok () state ∧
    state.construction.events = [.begin 0, .begin 1, .write 1 0, .write 1 1, .write 0 0,
      .begin 2, .write 2 0, .write 2 1, .write 0 1, .publish 0] := by
  refine ⟨witnessState (runModule 40 nestedConfig .initial), ?_, ?_⟩ <;>
    unfold witnessState nestedConfig nestedGlobal nestedGlobalOperand witnessEntry witnessEntryContext <;> cbv

#print axioms witness_nestedGlobal
#print axioms witness_nestedGlobal_events

#print axioms witness_directGlobal
#print axioms witness_directGlobal_events

#print axioms witness_globalFillOnce

#print axioms globalReplay_sourceForest
#print axioms runModule_fixedSourceForest
end Goose.Proofs.ConstructionGhostSourceGlobal
