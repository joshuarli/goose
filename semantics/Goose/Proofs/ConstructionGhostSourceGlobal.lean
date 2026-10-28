import Goose.Proofs.ConstructionGhostSourceMutual
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
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

theorem globalReplay_sourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor →
      descriptor.ty.nonfixed = false → ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    FixedSourceForest fuel config visits := by
  intro visit member descriptor found fixed
  dsimp only
  refine ⟨history_exists fuel config _ _ _ (supported visit.operand descriptor found fixed _), ?_⟩
  obtain ⟨tree, execution⟩ := fixedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand visit.before descriptor found fixed
  exact (visit_executes replay visit member).symm.trans execution

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

theorem globalReplay_materializedSourceForest {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (supported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global) count,
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count →
      ∀ environment, SupportedOperation config (.value environment descriptor.init)) :
    MaterializedSourceForest fuel config visits := by
  intro visit member descriptor count found nonfixed materialized
  dsimp only
  refine ⟨history_exists fuel config _ _ _ (supported visit.operand descriptor count found nonfixed materialized _), ?_⟩
  obtain ⟨tree, execution⟩ := materializedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand
    visit.before descriptor count found nonfixed materialized
  exact (visit_executes replay visit member).symm.trans execution

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

#print axioms witness_globalFillOnce

#print axioms globalReplay_sourceForest
#print axioms runModule_fixedSourceForest
end Goose.Proofs.ConstructionGhostSourceGlobal
