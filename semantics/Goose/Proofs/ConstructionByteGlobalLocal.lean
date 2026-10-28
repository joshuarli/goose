import Goose.Proofs.ConstructionByteNoTimeout
import Goose.Proofs.ConstructionAcceptedByteGlobalOutcome
import Goose.Proofs.ConstructionAcceptedByteGlobalTimeout
import Goose.Proofs.ConstructionAcceptedByteGlobalRun

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem carrier_local (carrier : Carrier) : LocalConstructionAction (carrierValue carrier) := by
  cases carrier with
  | register value => exact LocalConstructionAction.pure value
  | completed id => exact carrierCompleted_local id
  | pendingNamed id => exact LocalConstructionAction.fault _

theorem constructByte_local (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) :
    LocalConstructionAction (constructLocal ⟨config.module, environment.vars⟩ environment.act (.varr (.int .u8)) origin
      (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr (fuel + 1) config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin))) := by
  simp only [constructLocal, producerCount?, literalCount]
  apply LocalConstructionAction.bind (newByteDestination_local config environment origin bytes.length)
  intro destination
  apply LocalConstructionAction.bind (buildExpr_byteOwner_local fuel config environment destination _ bytes bytesOrigin)
  intro result
  cases result
  apply LocalConstructionAction.bind (completedReceivingDestination_local destination)
  intro completed
  apply LocalConstructionAction.bind (publishCompleted_local origin completed)
  intro result
  cases result
  exact LocalConstructionAction.pure _

theorem freshAct_local : LocalConstructionAction freshAct := by
  intro state
  simp [freshAct, EvalM.get, EvalM.set, bind, pure]

theorem initGlobals_byteOwner_single_local (fuel : Nat) (config : EvalConfig) (id : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId)
    (declared : config.module.globals[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    LocalConstructionAction (initGlobals (fuel + 1) config [id]) := by
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, ordinaryProducerCount?, producerCount?, literalCount,
    materializeProducer, Option.isSome_some, ↓reduceIte]
  apply LocalConstructionAction.bind freshAct_local
  intro act
  simp only [bind, pure]
  apply LocalConstructionAction.bind (constructByte_local fuel config ⟨0, act, #[], [], []⟩ bytes descriptor.org bytesOrigin)
  intro carrier
  apply LocalConstructionAction.bind (carrier_local carrier)
  intro value
  apply LocalConstructionAction.bind (bindRoot_local (.global id) value)
  intro result
  exact LocalConstructionAction.pure _

theorem initGlobals_byteOwners_local (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig),
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) →
      LocalConstructionAction (initGlobals (fuel + 1) config (List.range' initialized count)) := by
  induction count with
  | zero =>
    intro fuel initialized config declarations
    simpa only [List.range'_zero, initGlobals] using LocalConstructionAction.pure ()
  | succ count ih =>
    intro fuel initialized config declarations
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    have tail : ∀ id, initialized + 1 ≤ id → id < (initialized + 1) + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    rw [List.range'_succ, initGlobals_head_factor]
    apply LocalConstructionAction.bind (initGlobals_byteOwner_single_local fuel config initialized descriptor bytes bytesOrigin
      declared ty initializer)
    intro result
    exact ih fuel (initialized + 1) config tail

theorem initGlobals_byteOwners_timeout_world (count fuel initialized : Nat) (config : EvalConfig)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declarations : ∀ id, initialized ≤ id → id < initialized + count →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals fuel config (List.range' initialized count) before = .stop .timeout after) :
    ∃ destination,
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config initialized after ambient types live [freshReceivingRegion activated destination] [] ∧
      FutureGlobalsClear config initialized after := by
  cases fuel with
  | zero =>
    cases count with
    | zero => simp [List.range'_zero, initGlobals, pure] at executed
    | succ count =>
      obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
        declarations initialized (Nat.le_refl _) (by omega)
      simp only [List.range'_succ] at executed
      exact initGlobals_byteOwner_timeout_world config initialized descriptor bytes bytesOrigin _ before after ambient types live
        world clear declared ty initializer executed
  | succ fuel =>
    have noTimeout := initGlobals_byteOwners_local count fuel initialized config declarations before
    rw [executed] at noTimeout
    exact (noTimeout rfl).elim

theorem acceptedByteGlobals_run_timeout_afterInit (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (after : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : runModule (fuel + 1) config .initial = .stop .timeout after) :
    ∃ initialized live,
      initGlobals (fuel + 1) config (List.range config.module.globals.size) .initial = .ok () initialized ∧
      AcceptedWorld config config.module.globals.size initialized [] (declaredRootTypes config.module) live [] [] ∧
      (getImplementation config config.module.entry >>= fun (_, implementation) => do
        let channels ← channelsFor config.layout 0 implementation.results.toList 0
        let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
        let carriers ← invokeCall (fuel + 1) config environment config.module.entry [] channels 0
        publishCarriers 0 carriers) initialized = .stop .timeout after := by
  rcases acceptedByteGlobals_runPrefix fuel config accepted declarations with ⟨initialized, live, done, world⟩ |
      ⟨completed, middle, live, bound, world, clear, stopped⟩
  · refine ⟨initialized, live, done, world, ?_⟩
    simpa only [runModule, bind, done] using executed
  · obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ := declarations completed bound
    have noTimeout := initGlobals_byteOwner_single_local fuel config completed descriptor bytes bytesOrigin declared ty initializer middle
    rw [stopped, executed] at noTimeout
    exact (noTimeout rfl).elim

#print axioms initGlobals_byteOwner_single_local
#print axioms initGlobals_byteOwners_local
#print axioms initGlobals_byteOwners_timeout_world
#print axioms acceptedByteGlobals_run_timeout_afterInit

end Goose.Proofs.ConstructionAcceptedExecution
