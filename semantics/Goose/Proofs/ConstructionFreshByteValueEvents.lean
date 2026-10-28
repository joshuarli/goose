import Goose.Proofs.ConstructionFreshByteConstructEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem carrierValue_events (carrier : Carrier) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (carrierValue carrier state)).construction.events = state.construction.events := by
  cases carrier with
  | completed id => exact carrierValue_completed_events id state
  | register value => simp [carrierValue, pure, Goose.Proofs.Exit.stepState]
  | pendingNamed id => simp [carrierValue, Goose.Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState]

theorem evalValue_byteOwner_fresh_events (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (before : ExecutionState) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (evalValue fuel config environment
        (.bytes (.varr (.int .u8)) bytes origin) before)).construction.events = before.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerTraceEvent before.construction.destinations.size event := by
  cases fuel with
  | zero =>
    refine ⟨[], ?_, by simp⟩
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, List.append_nil]
  | succ fuel =>
    obtain ⟨suffix, trace, valid⟩ := constructLocal_byteOwner_fresh_events fuel config initialized environment before bytes
      origin origin ambient types live regions pending world
    refine ⟨suffix, ?_, valid⟩
    simp only [evalValue, Ty.nonfixed, ↓reduceIte]
    change (Goose.Proofs.Exit.stepState ((constructLocal ⟨config.module, environment.vars⟩ environment.act
      (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes origin)
      (fun destination => buildExpr fuel config environment destination (.bytes (.varr (.int .u8)) bytes origin)) >>= carrierValue) before)).construction.events = _
    cases executed : constructLocal ⟨config.module, environment.vars⟩ environment.act
        (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes origin)
        (fun destination => buildExpr fuel config environment destination (.bytes (.varr (.int .u8)) bytes origin)) before with
    | ok carrier after =>
      simp only [executed, Goose.Proofs.Exit.stepState] at trace
      simp only [bind, executed]
      exact (carrierValue_events carrier after).trans trace
    | stop reason after => simpa only [bind, executed, Goose.Proofs.Exit.stepState] using trace
    | escape target carriers after => simpa only [bind, executed, Goose.Proofs.Exit.stepState] using trace
    | jump target kind after => simpa only [bind, executed, Goose.Proofs.Exit.stepState] using trace

#print axioms carrierValue_events
#print axioms evalValue_byteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
