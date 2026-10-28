import Goose.Proofs.ConstructionByteGlobalComplete

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwners_zero_complete (initialized count : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (declarations : ∀ id, initialized ≤ id → id < initialized + count →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before) :
    ∃ regions,
      let outcome := initGlobals 0 config (List.range' initialized count) before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config initialized after ambient types live regions [] ∧
      (match outcome with
       | .ok _ _ => count = 0 ∧ regions = [] ∧ FutureGlobalsClear config initialized after
       | .stop _ _ => 0 < count
       | .escape .. | .jump .. => False) := by
  cases count with
  | zero =>
    simp only [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
    exact ⟨[], world, trivial, rfl, clear⟩
  | succ count =>
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    let activated := { before with nextAct := before.nextAct + 1 }
    let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
    have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
    have localAction := newByteDestination_local config environment descriptor.org bytes.length activated
    cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value descriptor.org none
        (some bytes.length) activated with
    | stop reason after =>
      have actual : initGlobals 0 config (List.range' initialized (count + 1)) before = .stop reason after := by
        simp only [List.range'_succ, initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
          ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
          constructLocal, environment, activated, EvalConfig.layout] at created ⊢
        simp only [created]
      have finalWorld := newDestination_byteOwner_stopped_world config initialized environment.act descriptor.org bytes.length
        activated after reason ambient types live [] [] activeWorld created
      simp only [actual, Goose.Proofs.Exit.stepState]
      exact ⟨[], finalWorld, by omega⟩
    | ok destination after =>
      have finalWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value descriptor.org
        (some bytes.length) initialized activated after destination ambient types live [] [] activeWorld created
      have actual : initGlobals 0 config (List.range' initialized (count + 1)) before = .stop .timeout after := by
        simp only [List.range'_succ, initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
          ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
          constructLocal, environment, activated, EvalConfig.layout] at created ⊢
        simp only [created, buildExpr, timeout, EvalM.stop]
      simp only [actual, Goose.Proofs.Exit.stepState]
      exact ⟨[freshReceivingRegion activated destination], finalWorld, by omega⟩
    | escape target carriers after | jump target kind after =>
      rw [created] at localAction
      cases localAction

theorem initGlobals_byteOwners_complete (fuel initialized count : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (bound : initialized + count ≤ config.module.globals.size)
    (declarations : ∀ id, initialized ≤ id → id < initialized + count →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before) :
    ∃ completed nextLive regions,
      let outcome := initGlobals fuel config (List.range' initialized count) before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + count ∧
      AcceptedWorld config completed after ambient types nextLive regions [] ∧
      (match outcome with
       | .ok _ _ => completed = initialized + count ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop _ _ => completed < initialized + count
       | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    obtain ⟨regions, finalWorld, final⟩ :=
      initGlobals_byteOwners_zero_complete initialized count config before ambient types live declarations world clear
    refine ⟨initialized, live, regions, Nat.le_refl _, by omega, finalWorld, ?_⟩
    cases outcome : initGlobals 0 config (List.range' initialized count) before with
    | ok value after =>
      cases value
      simp only [outcome, Goose.Proofs.Exit.stepState] at final ⊢
      obtain ⟨empty, regionsEmpty, finalClear⟩ := final
      exact ⟨by omega, regionsEmpty, finalClear⟩
    | stop stop after =>
      simp only [outcome] at final ⊢
      omega
    | escape target carriers after | jump target kind after =>
      simp only [outcome] at final
  | succ fuel =>
    exact initGlobals_byteOwners_positive_complete fuel initialized count config before ambient types live bound declarations world clear

#print axioms initGlobals_byteOwners_zero_complete
#print axioms initGlobals_byteOwners_complete

end Goose.Proofs.ConstructionAcceptedExecution
