import Goose.Proofs.ConstructionGhostGlobalCallHistory
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionGhostModuleCalls
open Goose.Construct Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostArguments
open Goose.Proofs.ConstructionInvocationReplay

def moduleAfterEntryCall (result : ExecutionStep (List Carrier)) : ExecutionStep Unit :=
  match result with
  | .ok carriers state => publishCarriers 0 carriers state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem runModule_globalAndEntryArgumentReplay (fuel : Nat) (config : EvalConfig) (before initialized lookupReady callStart callLookupReady argumentsReady : ExecutionState)
    (entryId : Goose.Core.ImplId) (entryImpl : Impl) (entryChannels callableChannels : List Channel)
    (globals : initGlobals (fuel + 1) config (List.range config.module.globals.size) before = .ok () initialized)
    (entryLookup : getImplementation config config.module.entry initialized = .ok (entryId, entryImpl) lookupReady)
    (entryPreparation : channelsFor config.layout 0 entryImpl.results.toList 0 lookupReady = .ok entryChannels callStart)
    (callLookup : getImplementation config config.module.entry callStart = .ok (entryId, entryImpl) callLookupReady)
    (arity : entryChannels.length = entryImpl.results.size)
    (prepared : prepareCallableChannels ⟨0, 0, #[], [], []⟩ entryChannels entryImpl 0 callLookupReady = .ok callableChannels argumentsReady) :
    ∃ globalOutcome globalVisits argumentOutcome argumentVisits,
      OperandReplay (globalInitializer (fuel + 1) config) 0 (List.range config.module.globals.size) [] before globalOutcome globalVisits ∧
      FixedGlobalForest (fuel + 1) config globalVisits ∧ MaterializedGlobalForest (fuel + 1) config globalVisits ∧
      ArgumentReplay config ⟨0, 0, #[], [], []⟩ entryImpl.vars fuel 0 entryImpl.params.toList [] argumentsReady argumentOutcome argumentVisits ∧
      (globalVisits.map Invocation.ordinal).Nodup ∧ (argumentVisits.map ArgumentInvocation.ordinal).Nodup ∧
      runModule (fuel + 1) config before = moduleAfterEntryCall
        (callArgumentsContinuation fuel config entryId entryImpl entryChannels callableChannels 0 argumentOutcome) := by
  obtain ⟨globalOutcome, globalVisits, globalReplay, fixed, materialized, globalOrder, globalOnce, globalExecution⟩ :=
    runModule_globalForests (fuel + 1) config before
  obtain ⟨argumentOutcome, argumentVisits, argumentReplay, argumentOrder, argumentOnce, callExecution⟩ :=
    invokeCall_argumentReplay fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] entryChannels 0
      callStart callLookupReady argumentsReady entryId entryImpl callableChannels callLookup arity prepared
  refine ⟨globalOutcome, globalVisits, argumentOutcome, argumentVisits, globalReplay, fixed, materialized,
    argumentReplay, globalOnce, argumentOnce, ?_⟩
  simp only [runModule, bind, globals, entryLookup, entryPreparation, callExecution, moduleAfterEntryCall]
  cases callArgumentsContinuation fuel config entryId entryImpl entryChannels callableChannels 0 argumentOutcome <;> rfl

private def witnessModule : Module :=
  ⟨#[], #[], #[⟨"global", .varr (.int .i64), .immutable,
    .blockE (.mk 0 [.print [.text "global"] 0]
      (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0, 0⟩],
    #[⟨"entry", #[], #[], #[], .mk 0 [.print [.text "entry"] 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem moduleCallWitness :
    ∃ after, runModule 100 ⟨.release, witnessModule⟩ .initial = .ok () after ∧
      after.construction.stdout.data.toList = [103, 108, 111, 98, 97, 108, 10, 101, 110, 116, 114, 121, 10] := by
  refine ⟨witnessState (runModule 100 ⟨.release, witnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold witnessState witnessModule <;> cbv

#print axioms moduleCallWitness
#print axioms runModule_globalAndEntryArgumentReplay
end Goose.Proofs.ConstructionGhostModuleCalls
