import Goose.Proofs.ConstructionGhostModuleEventOwnership

namespace Goose.Proofs.ConstructionGhostRecursiveGlobalOwnershipWitness
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostModuleEventOwnership
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostEventOwnership
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionInvocationReplay

private def element : Ty := .varr (.int .u8)
private def bytes : Expr := .bytes element [65, 66] 0
private def source : Expr := .call 1 [] 0
private def global : Global := ⟨"global", element, .immutable, source, 0⟩
private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def sourceContext : Context := ⟨1, "source", [], [], []⟩
private def entry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def producer : Impl := ⟨"source", #[], #[⟨element, .value, none⟩], #[], .mk 1 [] (some bytes), .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global], #[entry, producer], #[entryContext, sourceContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem argumentsSyntax : ∀ id actual start ready,
    getImplementation config 1 start = .ok (id, actual) ready → ArgumentSyntax config actual.params.toList [] := by
  intro id actual start ready lookup
  obtain ⟨context, found, idEq, implemented⟩ := implementation_lookup_source config 1 start ready id actual lookup
  have contextEq : context = sourceContext := by simpa [config] using found.symm
  subst context
  subst id
  have implEq : actual = producer := by simpa [config, sourceContext] using implemented.symm
  subst actual
  exact .nil

private theorem closed : ClosedModuleWithTails config := by
  intro contextId context implementation found implemented
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using found.symm
      subst context
      have implEq : implementation = entry := by simpa [config, entryContext] using implemented.symm
      subst implementation
      exact ⟨0, [], none, rfl, (by simp), .none⟩
  | succ n =>
      cases n with
      | zero =>
          have contextEq : context = sourceContext := by simpa [config] using found.symm
          subst context
          have implEq : implementation = producer := by simpa [config, sourceContext] using implemented.symm
          subst implementation
          exact ⟨1, [], some bytes, rfl, (by simp), .constructed bytes (.bytes _ _ _) (.bytes _ _ _) (.bytes _ _ _)⟩
      | succ n => simp [config] at found

private theorem globalDescriptor (id : Goose.Core.GlobalId) (descriptor : Global)
    (found : config.module.globals[id]? = some descriptor) : descriptor = global := by
  cases id with
  | zero => simpa [config] using found.symm
  | succ n => simp [config] at found

private theorem globalSyntax : ∀ (id : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[id]? = some descriptor → ValueSyntax config descriptor.init := by
  intro id descriptor found
  have same := globalDescriptor id descriptor found
  subst descriptor
  exact .channelCall 1 [] 0 argumentsSyntax

private theorem globalBuilder : ∀ (id : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[id]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? 40 ⟨config.module, #[]⟩ descriptor.init = none → DeclarationBuilderSyntax config descriptor.init := by
  intro id descriptor found nonfixed direct
  have same := globalDescriptor id descriptor found
  subst descriptor
  exact .channelCall 1 [] 0 argumentsSyntax

theorem recursiveGlobal_witness : ∃ outcome visits chunks continuation,
    OperandReplay (globalInitializer 40 config) 0 [0] [] .initial outcome visits ∧
    FixedSourceForest 40 config visits ∧ MaterializedSourceForest 40 config visits ∧ DirectSourceForest 40 config visits ∧
    ChunksAlign visits chunks ∧ OwnsEvents visits chunks ∧
    visits.map Invocation.operand = [0].take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
    (stepState (runModule 40 config .initial)).construction.events = chunks.flatten ++ continuation ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    ordinaryProducerCount? 40 ⟨config.module, #[]⟩ source = none ∧ visits ≠ [] := by
  obtain ⟨outcome, visits, chunks, continuation, replay, fixed, materialized, direct, aligned, ownership, ordered, once, finalEq, moduleEq, unique, continuationUnique⟩ :=
    runModule_globalSyntaxOwnership 40 config .initial closed globalSyntax globalBuilder
  refine ⟨outcome, visits, chunks, continuation, ?_, fixed, materialized, direct, aligned, ownership, ?_, once, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [config] using replay
  · simpa [config] using ordered
  · have sameStep : ∀ step : ExecutionStep Unit, stepState step = Goose.Proofs.Exit.stepState step := by
      intro step
      cases step <;> rfl
    rw [sameStep]
    simpa [ExecutionState.initial, ConstructionState.initial] using moduleEq
  · simp only [stepState, config, entryContext, sourceContext, entry, producer, global, source, bytes, element]
    cbv
  · simp only [stepState, config, entryContext, sourceContext, entry, producer, global, source, bytes, element]
    cbv
  · simp only [config, entryContext, sourceContext, entry, producer, global, source, bytes, element]
    cbv
  · intro empty
    subst visits
    have concrete : OperandReplay (globalInitializer 40 config) 0 [0] [] .initial outcome [] := by simpa [config] using replay
    cases concrete

#print axioms recursiveGlobal_witness
end Goose.Proofs.ConstructionGhostRecursiveGlobalOwnershipWitness
