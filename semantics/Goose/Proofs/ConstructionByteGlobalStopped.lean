import Goose.Proofs.ConstructionByteGlobalStoppedWorld
import Goose.Proofs.ConstructionByteLocalSuccess
import Goose.Proofs.ConstructionAcceptedByteGlobalOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem initGlobals_byteOwner_single_stopped_world (fuel : Nat) (config : EvalConfig) (initialized : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (declared : config.module.globals[initialized]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals (fuel + 1) config [initialized] before = .stop stop after) :
    ∃ regions, AcceptedWorld config initialized after ambient types live regions [] := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  let action := constructLocal ⟨config.module, environment.vars⟩ environment.act (.varr (.int .u8)) descriptor.org
    (.bytes (.varr (.int .u8)) bytes bytesOrigin)
    (fun destination => buildExpr (fuel + 1) config environment destination (.bytes (.varr (.int .u8)) bytes bytesOrigin))
  have equivalent : initGlobals (fuel + 1) config [initialized] before =
      (action >>= fun carrier => do
        let value ← carrierValue carrier
        bindRoot (.global initialized) value
        pure ()) activated := by
    simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
      ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
      action, environment, activated, constructLocal, carrierValue]
  rw [equivalent] at executed
  cases result : action activated with
  | stop reason final =>
    simp only [bind, result, ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value descriptor.org none
        (some bytes.length) activated with
    | stop reason final =>
      have created' := created
      simp only [EvalConfig.layout] at created'
      simp only [action, constructLocal, producerCount?, literalCount, bind, created', ExecutionStep.stop.injEq] at result
      obtain ⟨rfl, rfl⟩ := result
      exact ⟨[], newDestination_byteOwner_stopped_world config initialized environment.act descriptor.org bytes.length activated final reason
        ambient types live [] [] activeWorld created⟩
    | escape address carriers final =>
      have localAction := newByteDestination_local config environment descriptor.org bytes.length activated
      rw [created] at localAction; cases localAction
    | jump target kind final =>
      have localAction := newByteDestination_local config environment descriptor.org bytes.length activated
      rw [created] at localAction; cases localAction
    | ok destination allocated =>
      exact ⟨[freshReceivingRegion activated destination],
        constructLocal_byteOwner_stopped_afterAllocation_global fuel config initialized environment activated allocated final bytes descriptor.org
          bytesOrigin destination reason ambient types live [] [] activeWorld created result⟩
  | escape address carriers final => simp only [bind, result, reduceCtorEq] at executed
  | jump target kind final => simp only [bind, result, reduceCtorEq] at executed
  | ok carrier final =>
    obtain ⟨finalWorld, finalFrame, stored, sameCarrier, sampled, backed, storage, named, valueType⟩ :=
      constructLocal_byteOwner_success_world fuel config initialized environment bytes descriptor.org bytesOrigin
        activated final carrier ambient types live [] [] activeWorld result
    subst carrier
    simp only [bind, result, carrierValue, sampled, pure] at executed
    have bound : ∃ next, bindRoot (.global initialized) (.stored stored) final = .ok () next := by
      simp only [bindRoot, EvalM.get, bind]
      split <;> simp [setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind]
    obtain ⟨next, bound⟩ := bound
    simp only [bound, reduceCtorEq] at executed

theorem initGlobals_byteOwners_stopped_world (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (before after : ExecutionState) (stop : Goose.Core.Stop)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) →
      initGlobals (fuel + 1) config (List.range' initialized count) before = .stop stop after →
      ∃ completed nextLive regions, initialized ≤ completed ∧ completed < initialized + count ∧
        AcceptedWorld config completed after ambient types nextLive regions [] := by
  induction count with
  | zero =>
    intro fuel initialized config before after stop ambient types live world clear declarations executed
    simp [List.range'_zero, initGlobals, pure] at executed
  | succ count ih =>
    intro fuel initialized config before after stop ambient types live world clear declarations executed
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    have tail : ∀ id, initialized + 1 ≤ id → id < (initialized + 1) + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    rw [List.range'_succ] at executed
    have split := initGlobals_byteOwner_split fuel config initialized descriptor bytes bytesOrigin
      (List.range' (initialized + 1) count) before (.stop stop after) ambient types live world clear declared ty initializer executed
    rcases split with head | ⟨middle, tailRun, nextWorld, nextClear⟩
    · obtain ⟨regions, finalWorld⟩ := initGlobals_byteOwner_single_stopped_world fuel config initialized descriptor
        bytes bytesOrigin before after stop ambient types live world declared ty initializer head
      exact ⟨initialized, live, regions, by omega, by omega, finalWorld⟩
    · obtain ⟨completed, nextLive, regions, lower, upper, finalWorld⟩ :=
        ih fuel (initialized + 1) config middle after stop ambient types _ nextWorld nextClear tail tailRun
      exact ⟨completed, nextLive, regions, by omega, by omega, finalWorld⟩

#print axioms initGlobals_byteOwners_stopped_world
#print axioms initGlobals_byteOwner_single_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution
