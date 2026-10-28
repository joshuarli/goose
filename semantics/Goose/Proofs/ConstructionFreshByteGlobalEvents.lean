import Goose.Proofs.ConstructionFreshByteLocalEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private def bindByteGlobal (root : Goose.Core.RootInst) (carrier : Carrier) : EvalM Unit := do
  let value ← carrierValue carrier
  bindRoot root value
  pure ()

private theorem bindByteGlobal_events (root : Goose.Core.RootInst) (carrier : Carrier) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (bindByteGlobal root carrier state)).construction.events = state.construction.events := by
  unfold bindByteGlobal
  rw [bind_events_frame (carrierValue carrier)]
  · exact carrierValue_events carrier state
  · intro value current
    rw [bind_events_frame (bindRoot root value)]
    · exact bindRoot_events root value current
    · intro result after
      simp [pure, Goose.Proofs.Exit.stepState]

theorem initGlobal_byteOwner_fresh_events (fuel initialized global : Nat) (config : EvalConfig)
    (descriptor : Global) (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (declared : config.module.globals[global]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (initGlobals fuel config [global] before)).construction.events =
        before.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerTraceEvent before.construction.destinations.size event := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  obtain ⟨suffix, trace, valid⟩ := constructLocal_byteOwner_fresh_events fuel config initialized environment activated bytes
    descriptor.org bytesOrigin ambient types live [] [] activeWorld
  refine ⟨suffix, ?_, valid⟩
  have frame := bind_events_frame
    (constructLocal ⟨config.module, environment.vars⟩ environment.act (.varr (.int .u8)) descriptor.org
      (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr fuel config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin)))
    (bindByteGlobal (.global global)) activated (bindByteGlobal_events (.global global))
  rw [← frame] at trace
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
    ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte]
  simpa only [bindByteGlobal, bind, pure, EvalConfig.layout, environment, activated] using trace

#print axioms initGlobal_byteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
