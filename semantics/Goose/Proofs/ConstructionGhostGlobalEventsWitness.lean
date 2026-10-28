import Goose.Proofs.ConstructionGhostGlobalEvents

namespace Goose.Proofs.ConstructionGhostGlobalEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostGlobalEvents
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def global : Global := ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65, 66] 0, 0⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem descriptor (id : Goose.Core.GlobalId) (value : Global) (found : config.module.globals[id]? = some value) :
    value = global := by
  cases id with
  | zero => simpa [config] using found.symm
  | succ n => simp [config] at found

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
      subst actualImplementation
      exact ⟨0, [], none, rfl, by simp, .none⟩
  | succ n => simp [config] at found

private theorem globalSyntax : ∀ (id : Goose.Core.GlobalId) (value : Global), config.module.globals[id]? = some value → ValueSyntax config value.init := by
  intro id value found
  have same := descriptor id value found
  subst value
  exact .bytes (.varr (.int .u8)) [65, 66] 0

private theorem directSupported (fuel : Nat) : ∀ (id : Goose.Core.GlobalId) (value : Global), config.module.globals[id]? = some value →
    value.ty.nonfixed = true → ordinaryProducerCount? fuel ⟨config.module, #[]⟩ value.init = none →
    ∀ environment destination, SupportedOperation config (.builder environment destination value.init) := by
  intro id value found nonfixed direct environment destination
  have same := descriptor id value found
  subst value
  exact .builderBytes environment destination (.varr (.int .u8)) [65, 66] 0

private theorem argumentsSyntax : ∀ id actualImplementation start ready,
    getImplementation config 0 start = .ok (id, actualImplementation) ready → ArgumentSyntax config actualImplementation.params.toList [] := by
  intro id actualImplementation start ready lookup
  obtain ⟨actualContext, found, idEqual, implFound⟩ := implementation_lookup_source config 0 start ready id actualImplementation lookup
  have contextEq : actualContext = context := by simpa [config] using found.symm
  subst actualContext
  subst id
  have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
  subst actualImplementation
  exact .nil

theorem globalEventChunks_nonempty : ∃ outcome visits chunks after,
    OperandReplay (globalInitializer 40 config) 0 [0] [] .initial outcome visits ∧
    DirectSourceForest 40 config visits ∧
    visits.map Invocation.operand = [0].take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
    ChunksAlign visits chunks ∧ (Goose.Proofs.Exit.stepState outcome).construction.events = chunks.flatten ∧
    chunks.flatten = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    runModule 40 config .initial = .ok () after ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  obtain ⟨outcome, visits, chunks, replay, fixed, materialized, direct, ordered, once, aligned, finalEq, execution, entry⟩ :=
    runModule_globalEventChunks 40 config .initial closed globalSyntax (directSupported 40) context implementation rfl rfl argumentsSyntax
  refine ⟨outcome, visits, chunks, stepState (runModule 40 config .initial), ?_, direct, ?_, once, aligned, finalEq, ?_, ?_, ?_⟩
  · simpa [config] using replay
  · simpa [config] using ordered
  · have prefixEq : (Goose.Proofs.Exit.stepState outcome).construction.events = chunks.flatten := by simpa [ExecutionState.initial, ConstructionState.initial] using finalEq
    rw [← prefixEq, ← replay.execute]
    unfold globalInitializer config context implementation global
    cbv
  · unfold stepState config context implementation global
    cbv
  · unfold stepState config context implementation global
    cbv

#print axioms globalEventChunks_nonempty
end Goose.Proofs.ConstructionGhostGlobalEventsWitness
