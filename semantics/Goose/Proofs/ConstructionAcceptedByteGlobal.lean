import Goose.Proofs.ConstructionAcceptedGlobalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwner_head (fuel : Nat) (config : EvalConfig) (initialized : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (rest : List Goose.Core.GlobalId)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals (fuel + 1) config (initialized :: rest) before = .ok () after) :
    ∃ middle, initGlobals (fuel + 1) config rest middle = .ok () after ∧
      AcceptedWorld config (initialized + 1) middle ambient types
        (fun root => root = .global initialized ∨ live root) [] [] ∧
      FutureGlobalsClear config (initialized + 1) middle := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  have activeClear := clear.freshAct
  simp only [initGlobals, declared, ty, Ty.nonfixed, initializer, freshAct, EvalM.get, EvalM.set, bind, pure,
    ordinaryProducerCount?, producerCount?, literalCount, materializeProducer, Option.isSome_some, ↓reduceIte,
    constructLocal] at executed
  cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value descriptor.org none
      (some bytes.length) activated with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [environment, activated, EvalConfig.layout] at created
    simp only [created] at executed
    cases executed
  | ok id allocated =>
    simp only [environment, activated, EvalConfig.layout] at created
    simp only [created] at executed
    cases constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
    | stop reason state | escape reason carriers state | jump reason kind state =>
      simp only [environment] at constructed
      simp only [constructed] at executed
      cases executed
    | ok result built =>
      cases result
      simp only [environment] at constructed
      simp only [constructed] at executed
      cases completed : completedReceivingDestination id built with
      | stop reason state | escape reason carriers state | jump reason kind state =>
        simp only [completed] at executed
        cases executed
      | ok selected checked =>
        simp only [completed] at executed
        have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value descriptor.org
          (some bytes.length) activated allocated id created
        subst id
        obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value descriptor.org
          (some bytes.length) activated allocated activated.construction.destinations.size activeWorld.ownership.source.structural.1.1.1 created
        obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value descriptor.org
          (some bytes.length) activated allocated activated.construction.destinations.size (.int .u8) rfl created
        obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
          environment.act descriptor.org (some bytes.length) activated allocated activated.construction.destinations.size created
        have framePresent : allocated.construction.destinations[activated.construction.destinations.size]? = some frame.row := by
          rw [frame.destinations]; exact Array.getElem?_push_size
        have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
        subst row
        have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value descriptor.org
          (some bytes.length) initialized activated allocated activated.construction.destinations.size ambient types live [] [] activeWorld created
        have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value descriptor.org
          (some bytes.length) activated allocated activated.construction.destinations.size ambient types live [] [] activeWorld created
        obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes bytesOrigin activated allocated built
          frame activated.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
        have currentBuilt := frame.same_current builtFrame activated.construction.destinations.size current
        obtain ⟨sameId, sameState⟩ := completedReceivingDestination_self activated.construction.destinations.size built checked selected currentBuilt completed
        subst selected checked
        cases published : publishCarriers descriptor.org [.completed activated.construction.destinations.size] built with
        | stop reason state | escape reason carriers state | jump reason kind state =>
          simp only [published] at executed
          cases executed
        | ok result final =>
          cases result
          simp only [published, carrierValue, bind] at executed
          obtain ⟨finalWorld, ⟨finalFrame⟩, stored, sampled, backed, storage, named, valueType⟩ :=
            allocated_published_byteOwner_world fuel config initialized environment bytes descriptor.org bytesOrigin activated allocated built final
              activated.construction.destinations.size ambient types live [] [] activeWorld created constructed published
          simp only [sampled, pure] at executed
          have finalClear := activeClear.freshDestination finalFrame
          have globalBound := (Array.getElem?_eq_some_iff.mp declared).1
          have fresh := (finalClear initialized (Nat.le_refl _) globalBound).2
          have represented : ValueRepresentation descriptor.ty (.stored stored) := by
            rw [ty]
            exact .stored _ stored rfl valueType
          obtain ⟨middle, bound, nextWorld⟩ := bindRoot_freshGlobalStored_world config initialized final ambient types live descriptor stored
            finalWorld declared represented backed fresh
          simp only [bound] at executed
          exact ⟨middle, executed, nextWorld, finalClear.bindGlobal (.stored stored) bound⟩

theorem initGlobals_byteOwners (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (before after : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      initGlobals (fuel + 1) config (List.range' initialized count) before = .ok () after →
      ∃ nextLive, AcceptedWorld config (initialized + count) after ambient types nextLive [] [] ∧
        FutureGlobalsClear config (initialized + count) after := by
  induction count with
  | zero =>
    intro fuel initialized config before after ambient types live bound declarations world clear executed
    simp only [List.range'_zero, initGlobals, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact ⟨live, by simpa using world, by simpa using clear⟩
  | succ count ih =>
    intro fuel initialized config before after ambient types live bound declarations world clear executed
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    have tailDeclaration : ∀ id, initialized + 1 ≤ id → id < (initialized + 1) + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    simp only [List.range'_succ] at executed
    obtain ⟨middle, tail, nextWorld, nextClear⟩ := initGlobals_byteOwner_head fuel config initialized descriptor bytes bytesOrigin
      (List.range' (initialized + 1) count) before after ambient types live world clear declared ty initializer executed
    obtain ⟨nextLive, finalWorld, finalClear⟩ := ih fuel (initialized + 1) config middle after ambient types
      (fun root => root = .global initialized ∨ live root) (by omega) tailDeclaration nextWorld nextClear tail
    exact ⟨nextLive, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalWorld,
      by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalClear⟩

theorem initGlobals_byteOwners_initial (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (after : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals (fuel + 1) config (List.range config.module.globals.size) .initial = .ok () after) :
    ∃ live, AcceptedWorld config config.module.globals.size after [] (declaredRootTypes config.module) live [] [] ∧
      FutureGlobalsClear config config.module.globals.size after := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  have started := initial_acceptedWorld config accepted.accepted
  have clear := futureGlobalsClear_initial config
  have run : initGlobals (fuel + 1) config (List.range' 0 config.module.globals.size) .initial = .ok () after := by
    simpa only [List.range_eq_range'] using executed
  simpa only [Nat.zero_add] using initGlobals_byteOwners config.module.globals.size fuel 0 config .initial after []
    (declaredRootTypes config.module) (fun _ => False) (by simp) checked started clear run

#print axioms initGlobals_byteOwner_head
#print axioms initGlobals_byteOwners
#print axioms initGlobals_byteOwners_initial

end Goose.Proofs.ConstructionAcceptedExecution
