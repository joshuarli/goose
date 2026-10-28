import Goose.Proofs.ConstructionFreshRecursiveGlobalEvents
import Goose.Proofs.ConstructionAcceptedRecursiveGlobal
import Goose.Proofs.ConstructionFreshByteGlobalSequenceEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem initGlobals_recursive_fresh_events (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      ∃ suffix,
        (Goose.Proofs.Exit.stepState (initGlobals fuel config (List.range' initialized count) before)).construction.events =
          before.construction.events ++ suffix ∧ ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  induction count with
  | zero =>
    intro fuel initialized config accepted before ambient types live bound declarations world clear
    refine ⟨[], ?_, by simp⟩
    simp [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
  | succ count ih =>
    intro fuel initialized config accepted before ambient types live bound declarations world clear
    obtain ⟨descriptor, declared, initializer⟩ := declarations initialized (Nat.le_refl _) (by omega)
    have headTrace : ∃ suffix,
        (Goose.Proofs.Exit.stepState (initGlobals fuel config [initialized] before)).construction.events =
          before.construction.events ++ suffix ∧ ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
      rcases initializer with ⟨form, scalar⟩ | ⟨bytes, bytesOrigin, ty, init⟩
      · refine ⟨[], ?_, by simp⟩
        simpa only [List.append_nil] using initGlobal_recursiveScalar_events fuel initialized config descriptor before declared form scalar
      · obtain ⟨suffix, trace, valid⟩ := initGlobal_byteOwner_fresh_events fuel initialized initialized config descriptor bytes bytesOrigin
          before ambient types live world declared ty init
        exact ⟨suffix, trace, fun event member => ⟨before.construction.destinations.size, valid event member⟩⟩
    obtain ⟨first, firstTrace, firstValid⟩ := headTrace
    have tailDeclarations : ∀ id, initialized + 1 ≤ id → id < initialized + 1 + count →
        ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    obtain ⟨completed, nextLive, regions, lower, upper, headWorld, headFlow⟩ :=
      initGlobals_recursive_single fuel initialized config accepted before ambient types live descriptor world clear declared initializer
    have factor := initGlobals_head_factor fuel config initialized (List.range' (initialized + 1) count)
    simp only [List.range'_succ]
    rw [factor]
    cases head : initGlobals fuel config [initialized] before with
    | stop reason after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, firstValid⟩
      simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
    | escape target carriers after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, firstValid⟩
      simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
    | jump target kind after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, firstValid⟩
      simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
    | ok value middle =>
      cases value
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace headWorld headFlow
      obtain ⟨finished, regionsEq, nextClear⟩ := headFlow
      subst completed regions
      obtain ⟨tail, tailTrace, tailValid⟩ := ih fuel (initialized + 1) config accepted middle ambient types nextLive
        (by omega) tailDeclarations headWorld nextClear
      refine ⟨first ++ tail, ?_, ?_⟩
      · simp only [bind, head]
        rw [tailTrace, firstTrace]
        simp [List.append_assoc]
      · intro event member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact firstValid event member
        · exact tailValid event member

theorem initGlobals_recursive_initial_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor) :
    ∃ events,
      (Goose.Proofs.Exit.stepState (initGlobals fuel config (List.range config.module.globals.size) .initial)).construction.events = events ∧
      ∀ event ∈ events, ByteOwnerSequenceEvent event := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  obtain ⟨events, trace, valid⟩ := initGlobals_recursive_fresh_events config.module.globals.size fuel 0 config accepted
    .initial [] (declaredRootTypes config.module) (fun _ => False) (by simp) checked
    (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
  refine ⟨events, ?_, valid⟩
  simpa only [Nat.zero_add, ← List.range_eq_range', ExecutionState.initial, ConstructionState.initial, List.nil_append] using trace

#print axioms initGlobals_recursive_fresh_events
#print axioms initGlobals_recursive_initial_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
