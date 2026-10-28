import Goose.Proofs.ConstructionAcceptedByteTimeout
import Goose.Proofs.ConstructionAcceptedByteGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwner_timeout_world (config : EvalConfig) (initialized : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (rest : List Goose.Core.GlobalId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals 0 config (initialized :: rest) before = .stop .timeout after) :
    ∃ destination,
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config initialized after ambient types live [freshReceivingRegion activated destination] [] ∧
      FutureGlobalsClear config initialized after := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  have activeClear := clear.freshAct
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
    ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
    constructLocal] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value descriptor.org none
      (some bytes.length) activated with
  | stop reason state =>
    simp only [environment, activated, EvalConfig.layout] at created
    simp only [created] at executed
    cases executed
    exact (newDestination_byteOwner_ne_timeout config.layout environment.act descriptor.org bytes.length activated after created).elim
  | escape target carriers state | jump target kind state =>
    simp only [environment, activated, EvalConfig.layout] at created
    simp only [created] at executed
    cases executed
  | ok destination allocated =>
    have created' := created
    simp only [environment, activated, EvalConfig.layout] at created'
    simp only [created', buildExpr, timeout, EvalM.stop] at executed
    cases executed
    have fresh := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value descriptor.org
      (some bytes.length) initialized activated after destination ambient types live [] [] activeWorld created
    obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value descriptor.org
      (some bytes.length) activated after destination activeWorld.ownership.source.structural.1.1.1 created
    exact ⟨destination, fresh, activeClear.freshDestination frame⟩

theorem initGlobals_byteOwner_zero_ne_ok (config : EvalConfig) (initialized : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (rest : List Goose.Core.GlobalId)
    (before after : ExecutionState)
    (declared : config.module.globals[initialized]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    initGlobals 0 config (initialized :: rest) before ≠ .ok () after := by
  intro executed
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
    ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
    constructLocal] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value descriptor.org none
      (some bytes.length) activated <;>
    simp only [environment, activated, EvalConfig.layout] at created <;>
    simp only [created, buildExpr, timeout, EvalM.stop, reduceCtorEq] at executed

theorem acceptedByteGlobal_zero_run_timeout_world (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (after : ExecutionState)
    (declared : config.module.globals[0]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : runModule 0 config .initial = .stop .timeout after) :
    ∃ destination,
      let activated := { (ExecutionState.initial) with nextAct := ExecutionState.initial.nextAct + 1 }
      AcceptedWorld config 0 after [] (declaredRootTypes config.module) (fun _ => False)
        [freshReceivingRegion activated destination] [] ∧ FutureGlobalsClear config 0 after := by
  have nonempty : 0 < config.module.globals.size := (Array.getElem?_eq_some_iff.mp declared).1
  have range : List.range config.module.globals.size = 0 :: List.range' 1 (config.module.globals.size - 1) := by
    cases size : config.module.globals.size with
    | zero => omega
    | succ size => simp only [List.range_eq_range', List.range'_succ, Nat.succ_sub_one]
  let globals := List.range config.module.globals.size
  have initialized : initGlobals 0 config globals .initial = .stop .timeout after := by
    cases result : initGlobals 0 config globals .initial with
    | ok value state =>
      cases value
      have impossible := initGlobals_byteOwner_zero_ne_ok config 0 descriptor bytes bytesOrigin
        (List.range' 1 (config.module.globals.size - 1)) .initial state declared ty initializer
      exact (impossible (by simpa only [globals, range] using result)).elim
    | stop reason state =>
      have actualResult : initGlobals 0 config (List.range config.module.globals.size) .initial = .stop reason state := by
        simpa only [globals] using result
      simp only [runModule, bind, actualResult, ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      rfl
    | escape target carriers state =>
      have actualResult : initGlobals 0 config (List.range config.module.globals.size) .initial = .escape target carriers state := by
        simpa only [globals] using result
      simp only [runModule, bind, actualResult, reduceCtorEq] at executed
    | jump target kind state =>
      have actualResult : initGlobals 0 config (List.range config.module.globals.size) .initial = .jump target kind state := by
        simpa only [globals] using result
      simp only [runModule, bind, actualResult, reduceCtorEq] at executed
  have run : initGlobals 0 config (0 :: List.range' 1 (config.module.globals.size - 1)) .initial = .stop .timeout after := by
    simpa only [globals, range] using initialized
  exact initGlobals_byteOwner_timeout_world config 0 descriptor bytes bytesOrigin _ .initial after []
    (declaredRootTypes config.module) (fun _ => False) (initial_acceptedWorld config accepted.accepted)
    (futureGlobalsClear_initial config) declared ty initializer run

#print axioms acceptedByteGlobal_zero_run_timeout_world
#print axioms initGlobals_byteOwner_zero_ne_ok
#print axioms initGlobals_byteOwner_timeout_world

end Goose.Proofs.ConstructionAcceptedExecution
