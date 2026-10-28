import Goose.Proofs.ConstructionFreshByteBindingEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private def bindByteLocal (root : Goose.Core.RootInst) : Carrier → EvalM Flow
  | .completed destination => do
      let stored ← storedDestination destination
      bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })
      pure (.normal .unit)
  | _ => fault .flow

private theorem bindByteLocal_events (root : Goose.Core.RootInst) (carrier : Carrier) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (bindByteLocal root carrier state)).construction.events = state.construction.events := by
  cases carrier with
  | register value => simp [bindByteLocal, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | pendingNamed id => simp [bindByteLocal, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | completed id =>
    unfold bindByteLocal
    rw [bind_events_frame (storedDestination id)]
    · exact storedDestination_events id state
    · intro stored current
      rw [bind_events_frame (bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none }))]
      · exact bindRoot_events _ _ current
      · intro value after
        simp [pure, Goose.Proofs.Exit.stepState]

theorem execStmt_byteOwner_fresh_events (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (descriptor : LocalVar) (implementation : Impl)
    (before : ExecutionState) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (declared : environment.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (execStmt fuel config environment
        (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before)).construction.events =
          before.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerTraceEvent before.construction.destinations.size event := by
  cases fuel with
  | zero =>
    refine ⟨[], ?_, by simp⟩
    simp only [execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, List.append_nil]
  | succ fuel =>
    have rootState := rootOf_unchanged environment id before
    cases resolved : rootOf environment id before with
    | stop reason after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at rootState
      subst after
      refine ⟨[], ?_, by simp⟩
      simp only [execStmt, declared, bind, resolved, Goose.Proofs.Exit.stepState, List.append_nil]
    | escape target carriers after =>
      have localAction := rootOf_local environment id before
      rw [resolved] at localAction
      cases localAction
    | jump target kind after =>
      have localAction := rootOf_local environment id before
      rw [resolved] at localAction
      cases localAction
    | ok root after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at rootState
      subst after
      obtain ⟨suffix, trace, valid⟩ := constructLocal_byteOwner_fresh_events fuel config initialized environment before bytes
        origin bytesOrigin ambient types live regions pending world
      refine ⟨suffix, ?_, valid⟩
      have frame := bind_events_frame
        (constructLocal ⟨config.module, environment.vars⟩ environment.act (.varr (.int .u8)) origin
          (.bytes (.varr (.int .u8)) bytes bytesOrigin)
          (fun destination => buildExpr fuel config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin)))
        (bindByteLocal root) before (bindByteLocal_events root)
      rw [← frame] at trace
      simp only [execStmt, declared, ty, Ty.nonfixed, implementationFound, unnamed, ordinaryProducerCount?,
        producerCount?, literalCount, Option.isSome_some, ↓reduceIte, materializeProducer, bind, pure, resolved,
        Option.isNone_none, Option.isSome_none, Option.map_none, Bool.false_eq_true, Option.orElse_eq_orElse, Option.orElse]
      simp only [constructLocal, producerCount?, literalCount, eval_bind_assoc, eval_pure_bind, bindByteLocal] at trace
      simpa only [bind, pure, EvalConfig.layout] using trace

#print axioms execStmt_byteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
