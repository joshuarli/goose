import Goose.Proofs.ConstructionFreshByteGlobalEvents
import Goose.Proofs.ConstructionByteGlobalZeroComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem initGlobals_single_then (fuel : Nat) (config : EvalConfig) (global : Nat) (rest : List Nat)
    (descriptor : Global) (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId)
    (declared : config.module.globals[global]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    initGlobals fuel config (global :: rest) = initGlobals fuel config [global] >>= fun _ => initGlobals fuel config rest := by
  funext state
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, ordinaryProducerCount?, producerCount?, literalCount,
    materializeProducer, Option.isSome_some, ↓reduceIte, eval_bind_assoc, eval_pure_bind, bind, pure]
  repeat' first
    | rfl
    | split
    | simp_all

def ByteOwnerSequenceEvent (event : Goose.Core.ConstructionEvent) : Prop :=
  ∃ id, ByteOwnerTraceEvent id event

theorem initGlobals_byteOwners_fresh_events (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      ∃ suffix,
        (Goose.Proofs.Exit.stepState (initGlobals fuel config (List.range' initialized count) before)).construction.events =
          before.construction.events ++ suffix ∧ ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  induction count with
  | zero =>
    intro fuel initialized config before ambient types live bound declarations world clear
    refine ⟨[], ?_, by simp⟩
    simp [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
  | succ count ih =>
    intro fuel initialized config before ambient types live bound declarations world clear
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    obtain ⟨first, firstTrace, firstValid⟩ := initGlobal_byteOwner_fresh_events fuel initialized initialized config
      descriptor bytes bytesOrigin before ambient types live world declared ty initializer
    have tailDeclarations : ∀ id, initialized + 1 ≤ id → id < initialized + 1 + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    have singletonDeclarations : ∀ id, initialized ≤ id → id < initialized + 1 →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id lower (by omega)
    simp only [List.range'_succ]
    rw [initGlobals_single_then fuel config initialized _ descriptor bytes bytesOrigin declared ty initializer]
    cases head : initGlobals fuel config [initialized] before with
    | stop reason after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, ?_⟩
      · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
      · intro event member
        exact ⟨before.construction.destinations.size, firstValid event member⟩
    | escape target carriers after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, ?_⟩
      · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
      · intro event member
        exact ⟨before.construction.destinations.size, firstValid event member⟩
    | jump target kind after =>
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first, ?_, ?_⟩
      · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
      · intro event member
        exact ⟨before.construction.destinations.size, firstValid event member⟩
    | ok value middle =>
      cases value
      have completed := initGlobals_byteOwners_complete fuel initialized 1 config before ambient types live (by omega)
        singletonDeclarations world clear
      have head' : initGlobals fuel config (List.range' initialized 1) before = .ok () middle := by
        simpa [List.range'] using head
      simp only [head', Goose.Proofs.Exit.stepState] at completed
      obtain ⟨finished, nextLive, nextRegions, _, _, nextWorld, final⟩ := completed
      obtain ⟨finishedEq, regionsEq, nextClear⟩ := final
      subst finished nextRegions
      obtain ⟨tail, tailTrace, tailValid⟩ := ih fuel (initialized + 1) config middle ambient types nextLive
        (by omega) tailDeclarations nextWorld nextClear
      simp only [head, Goose.Proofs.Exit.stepState] at firstTrace
      refine ⟨first ++ tail, ?_, ?_⟩
      · simp only [bind, head]
        rw [tailTrace, firstTrace]
        simp [List.append_assoc]
      · intro event member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact ⟨before.construction.destinations.size, firstValid event member⟩
        · exact tailValid event member

theorem initGlobals_acceptedByteOwners_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (initGlobals fuel config (List.range config.module.globals.size) .initial)).construction.events = suffix ∧
      ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  obtain ⟨suffix, trace, valid⟩ := initGlobals_byteOwners_fresh_events config.module.globals.size fuel 0 config .initial []
    (declaredRootTypes config.module) (fun _ => False) (by simp) checked
    (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
  refine ⟨suffix, ?_, valid⟩
  simpa only [Nat.zero_add, ← List.range_eq_range', ExecutionState.initial, ConstructionState.initial, List.nil_append] using trace

#print axioms initGlobals_acceptedByteOwners_fresh_events
#print axioms initGlobals_byteOwners_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
