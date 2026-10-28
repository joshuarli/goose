import Goose.Proofs.ConstructionGhostBlockValueRecursiveEvents
import Goose.Proofs.ConstructionGhostConstructedArgumentEvents
import Goose.Proofs.ConstructionGhostCallSetup

namespace Goose.Proofs.ConstructionGhostBlockValueSetup
open Goose.Construct Goose.Proofs.ConstructionGhostBlockProducerTransition Goose.Proofs.ConstructionGhostBlockValueChannels
open Goose.Proofs.ConstructionGhostConstructedArgumentEvents Goose.Proofs.ConstructionGhostCallSetup

theorem blockValue_missingTypes (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState)
    (missing : blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = none) :
    evalValue (fuel + 1) config environment (.blockE block origin) before = .stop (.fault .shape) before := by
  simp [evalValue, missing, fault, EvalM.stop]

theorem blockValue_channelsTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) (types : List Ty) (terminal : ExecutionStep Value)
    (typesFound : blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : terminalValue (channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before) = some terminal) :
    evalValue (fuel + 1) config environment (.blockE block origin) before = terminal := by
  simp only [evalValue, typesFound, bind]
  cases result : channelsFor config.layout environment.act
    (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before <;>
    simp_all [terminalValue, bind]

theorem blockProducer_channelsTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) (channels : List Channel) (terminal : ExecutionStep (List Carrier))
    (prepared : terminalCall (prepareBlockProducerChannels channels origin before) = some terminal) :
    evalProduce (fuel + 1) config environment channels (.blockE block origin) before = terminal := by
  simp only [evalProduce, expressionOrigin, bind]
  change (prepareBlockProducerChannels channels origin >>= fun planned =>
    withBreakTarget environment.act .block planned
      (do let (flow, carriers) ← execResultBlock fuel config environment planned block
          match flow with | .normal _ => pure carriers | _ => fault .flow)
      (fun kind => do match kind with
        | .breakValue carriers => landCarriersInto origin planned carriers; pure carriers
        | .continueLoop => fault .flow)) before = _
  cases result : prepareBlockProducerChannels channels origin before <;> simp_all [terminalCall, bind]

theorem blockValue_producerTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before ready : ExecutionState) (types : List Ty) (channels : List Channel)
    (terminal : ExecutionStep Value)
    (typesFound : blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels ready)
    (result : terminalValue (evalProduce fuel config environment channels (.blockE block origin) ready) = some terminal) :
    evalValue (fuel + 1) config environment (.blockE block origin) before = terminal := by
  rw [blockValue_afterChannels fuel config environment block origin before ready types channels typesFound prepared]
  cases actual : evalProduce fuel config environment channels (.blockE block origin) ready <;> simp_all [terminalValue, bind]

theorem blockValue_setupClassification (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    (blockResultTypes? (max (fuel + 1) (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = none ∧
      evalValue (fuel + 2) config environment (.blockE block origin) before = .stop (.fault .shape) before) ∨
    (∃ types terminal, blockResultTypes? (max (fuel + 1) (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types ∧
      terminalValue (channelsFor config.layout environment.act
        (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before) = some terminal ∧
      evalValue (fuel + 2) config environment (.blockE block origin) before = terminal) ∨
    (∃ types channels channelsReady terminal,
      blockResultTypes? (max (fuel + 1) (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types ∧
      channelsFor config.layout environment.act (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady ∧
      terminalCall (prepareBlockProducerChannels channels origin channelsReady) = some terminal ∧
      terminalValue terminal = some (evalValue (fuel + 2) config environment (.blockE block origin) before)) ∨
    (∃ types channels channelsReady planned plannedReady,
      blockResultTypes? (max (fuel + 1) (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types ∧
      channelsFor config.layout environment.act (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels channelsReady ∧
      prepareBlockProducerChannels channels origin channelsReady = .ok planned plannedReady) := by
  cases typesFound : blockResultTypes? (max (fuel + 1) (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block with
  | none => exact Or.inl ⟨rfl, blockValue_missingTypes (fuel + 1) config environment block origin before typesFound⟩
  | some types =>
      cases prepared : channelsFor config.layout environment.act
        (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before with
      | ok channels ready =>
          cases plannedResult : prepareBlockProducerChannels channels origin ready with
          | ok planned plannedReady => exact Or.inr (Or.inr (Or.inr ⟨types, channels, ready, planned, plannedReady, rfl, prepared, plannedResult⟩))
          | stop reason state =>
              have terminal : terminalCall (prepareBlockProducerChannels channels origin ready) = some (.stop reason state) := by simp [plannedResult, terminalCall]
              have produced := blockProducer_channelsTerminal fuel config environment block origin ready channels _ terminal
              have final := blockValue_producerTerminal (fuel + 1) config environment block origin before ready types channels (.stop reason state)
                typesFound prepared (by simp [produced, terminalValue])
              exact Or.inr (Or.inr (Or.inl ⟨types, channels, ready, .stop reason state, rfl, prepared, terminal, by simp [final, terminalValue]⟩))
          | escape address carriers state =>
              have terminal : terminalCall (prepareBlockProducerChannels channels origin ready) = some (.escape address carriers state) := by simp [plannedResult, terminalCall]
              have produced := blockProducer_channelsTerminal fuel config environment block origin ready channels _ terminal
              have final := blockValue_producerTerminal (fuel + 1) config environment block origin before ready types channels (.escape address carriers state)
                typesFound prepared (by simp [produced, terminalValue])
              exact Or.inr (Or.inr (Or.inl ⟨types, channels, ready, .escape address carriers state, rfl, prepared, terminal, by simp [final, terminalValue]⟩))
          | jump target kind state =>
              have terminal : terminalCall (prepareBlockProducerChannels channels origin ready) = some (.jump target kind state) := by simp [plannedResult, terminalCall]
              have produced := blockProducer_channelsTerminal fuel config environment block origin ready channels _ terminal
              have final := blockValue_producerTerminal (fuel + 1) config environment block origin before ready types channels (.jump target kind state)
                typesFound prepared (by simp [produced, terminalValue])
              exact Or.inr (Or.inr (Or.inl ⟨types, channels, ready, .jump target kind state, rfl, prepared, terminal, by simp [final, terminalValue]⟩))
      | stop reason state =>
          have terminal : terminalValue (channelsFor config.layout environment.act
            (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before) = some (.stop reason state) := by simp [prepared, terminalValue]
          exact Or.inr (Or.inl ⟨types, .stop reason state, rfl, terminal,
            blockValue_channelsTerminal (fuel + 1) config environment block origin before types _ typesFound terminal⟩)
      | escape address carriers state =>
          have terminal : terminalValue (channelsFor config.layout environment.act
            (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before) = some (.escape address carriers state) := by simp [prepared, terminalValue]
          exact Or.inr (Or.inl ⟨types, .escape address carriers state, rfl, terminal,
            blockValue_channelsTerminal (fuel + 1) config environment block origin before types _ typesFound terminal⟩)
      | jump target kind state =>
          have terminal : terminalValue (channelsFor config.layout environment.act
            (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before) = some (.jump target kind state) := by simp [prepared, terminalValue]
          exact Or.inr (Or.inl ⟨types, .jump target kind state, rfl, terminal,
            blockValue_channelsTerminal (fuel + 1) config environment block origin before types _ typesFound terminal⟩)

theorem blockValue_zero (config : EvalConfig) (environment : RuntimeActivation) (block : Block)
    (origin : Goose.Core.OriginId) (before : ExecutionState) :
    evalValue 0 config environment (.blockE block origin) before = .stop .timeout before := by
  simp [evalValue, timeout, EvalM.stop]

theorem blockValue_one_afterChannels (config : EvalConfig) (environment : RuntimeActivation) (block : Block)
    (origin : Goose.Core.OriginId) (before ready : ExecutionState) (types : List Ty) (channels : List Channel)
    (typesFound : blockResultTypes? (max 0 (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels ready) :
    evalValue 1 config environment (.blockE block origin) before = .stop .timeout ready := by
  apply blockValue_producerTerminal 0 config environment block origin before ready types channels (.stop .timeout ready) typesFound prepared
  simp [evalProduce, timeout, EvalM.stop, terminalValue]

#print axioms blockValue_zero
#print axioms blockValue_one_afterChannels
#print axioms blockValue_setupClassification
#print axioms blockValue_missingTypes
#print axioms blockValue_channelsTerminal
#print axioms blockProducer_channelsTerminal
#print axioms blockValue_producerTerminal
end Goose.Proofs.ConstructionGhostBlockValueSetup
