import Goose.Proofs.ConstructionGhostGlobalHistorical
import Goose.Proofs.ConstructionGhostCallHistorical

namespace Goose.Proofs.ConstructionGhostGlobalCallHistory
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionGhostGlobalHistorical Goose.Proofs.ConstructionGhostCallHistorical
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ExitExecution

theorem moduleGlobals_beforeCallee (fuel callFuel : Nat) (config : EvalConfig) (before initialized lookupReady callStart : ExecutionState)
    (entryId : Goose.Core.ImplId) (entryImpl : Impl) (entryChannels : List Channel)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (callLookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (id : Goose.Core.ImplId) (implementation : Impl) (callableChannels refreshed : List Channel) (values : List Value)
    (globals : initGlobals fuel config (List.range config.module.globals.size) before = .ok () initialized)
    (entryLookup : getImplementation config config.module.entry initialized = .ok (entryId, entryImpl) lookupReady)
    (entryPreparation : channelsFor config.layout 0 entryImpl.results.toList 0 lookupReady = .ok entryChannels callStart)
    (callLookup : getImplementation config context callStart = .ok (id, implementation) callLookupReady)
    (prepared : prepareCallableChannels environment channels implementation origin callLookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments callFuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      (visits.map fun visit => visit.before.nextAct).Nodup ∧
      ∀ visit ∈ visits, visit.before.nextAct < activationReady.nextAct := by
  obtain ⟨outcome, visits, replay, unique, earlier⟩ := completedGlobals_activationBounds fuel config before initialized globals
  have lookupBound := counter_stateQuery _ (stateQuery_getImplementation config config.module.entry) initialized
  simp only [entryLookup, Goose.Proofs.Exit.stepState] at lookupBound
  have channelsBound := counter_channelsFor config.layout 0 entryImpl.results.toList 0 lookupReady
  simp only [entryPreparation, Goose.Proofs.Exit.stepState] at channelsBound
  have frontier := invokeCall_activation_frontier callFuel config environment context arguments channels origin
    callStart callLookupReady argumentsReady valuesReady activationReady id implementation callableChannels refreshed values
    callLookup prepared argumentsResult refresh
  refine ⟨outcome, visits, replay, unique, ?_⟩
  intro visit member
  exact Nat.lt_of_lt_of_le (earlier visit member) (Nat.le_trans lookupBound (Nat.le_trans channelsBound frontier))

theorem moduleGlobals_beforeEntryActivation (fuel : Nat) (config : EvalConfig)
    (before initialized lookupReady callStart callLookupReady argumentsReady valuesReady activationReady : ExecutionState)
    (entryId : Goose.Core.ImplId) (entryImpl : Impl) (entryChannels callableChannels refreshed : List Channel) (values : List Value)
    (globals : initGlobals fuel config (List.range config.module.globals.size) before = .ok () initialized)
    (entryLookup : getImplementation config config.module.entry initialized = .ok (entryId, entryImpl) lookupReady)
    (entryPreparation : channelsFor config.layout 0 entryImpl.results.toList 0 lookupReady = .ok entryChannels callStart)
    (callLookup : getImplementation config config.module.entry callStart = .ok (entryId, entryImpl) callLookupReady)
    (prepared : prepareCallableChannels ⟨0, 0, #[], [], []⟩ entryChannels entryImpl 0 callLookupReady = .ok callableChannels argumentsReady)
    (argumentsResult : evalArguments fuel config ⟨0, 0, #[], [], []⟩ entryImpl.vars entryImpl.params.toList [] argumentsReady = .ok values valuesReady)
    (refresh : refreshCallableChannels callableChannels 0 valuesReady = .ok refreshed activationReady) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      (visits.map fun visit => visit.before.nextAct).Nodup ∧
      ∀ visit ∈ visits, visit.before.nextAct < activationReady.nextAct :=
  moduleGlobals_beforeCallee fuel fuel config before initialized lookupReady callStart entryId entryImpl entryChannels
    ⟨0, 0, #[], [], []⟩ config.module.entry [] entryChannels 0 callLookupReady argumentsReady valuesReady activationReady
    entryId entryImpl callableChannels refreshed values globals entryLookup entryPreparation callLookup prepared argumentsResult refresh

private def witnessModule : Module :=
  ⟨#[], #[], #[⟨"global", .int .i64, .immutable, .lit .i64 7, 0⟩],
    #[⟨"entry", #[], #[], #[], .mk 0 [.print [.text "entry"] 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem globalAndEntryWitness :
    ∃ after, runModule 100 ⟨.release, witnessModule⟩ .initial = .ok () after ∧
      after.nextAct = 2 ∧ after.construction.stdout.data.toList = [101, 110, 116, 114, 121, 10] := by
  refine ⟨witnessState (runModule 100 ⟨.release, witnessModule⟩ .initial), ?_, ?_, ?_⟩ <;>
    unfold witnessState witnessModule <;> cbv

#print axioms globalAndEntryWitness
#print axioms moduleGlobals_beforeEntryActivation
#print axioms moduleGlobals_beforeCallee
end Goose.Proofs.ConstructionGhostGlobalCallHistory
