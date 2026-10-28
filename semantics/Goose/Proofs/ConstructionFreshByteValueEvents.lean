import Goose.Proofs.ConstructionFreshBytePublishEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

def ByteOwnerTraceEvent (id : Nat) : Goose.Core.ConstructionEvent → Prop
  | .begin actual => actual = id
  | .write actual _ => actual = id
  | .publish actual => actual = id
  | _ => False

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
    cases created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
        (some bytes.length) before with
    | stop reason after =>
      have trace := newDestination_byteOwner_stopped_events config.layout environment.act origin bytes.length before after reason created
      have created' := created
      simp only [EvalConfig.layout] at created'
      refine ⟨[], ?_, by simp⟩
      simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created',
        Goose.Proofs.Exit.stepState, List.append_nil]
      exact trace
    | escape target carriers after =>
      have localAction := newByteDestination_local config environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | jump target kind after =>
      have localAction := newByteDestination_local config environment origin bytes.length before
      rw [created] at localAction
      cases localAction
    | ok destination allocated =>
      have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
        (some bytes.length) before allocated destination created
      subst destination
      let id := before.construction.destinations.size
      have allocatedEvents := newDestination_byteOwner_success_events config.layout environment.act origin bytes.length before allocated id created
      have created' := created
      simp only [EvalConfig.layout] at created'
      cases fuel with
      | zero =>
        refine ⟨[.begin id], ?_, ?_⟩
        · simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created',
            buildExpr, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
          exact allocatedEvents
        · intro event member
          simp only [List.mem_singleton] at member
          subst event
          rfl
      | succ fuel =>
        obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
        obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) before allocated id (.int .u8) rfl created
        obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
          environment.act origin (some bytes.length) before allocated id created
        have framePresent : allocated.construction.destinations[id]? = some frame.row := by
          rw [frame.destinations]; exact Array.getElem?_push_size
        have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
        subst row
        have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
        have opened : frame.row.progress = .open 0 := by rw [← readySame]; exact ready.opened
        have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
          (some bytes.length) initialized before allocated id ambient types live regions pending world created
        have current := newDestination_current_self config initialized environment.act (.varr (.int .u8))
          .value origin (some bytes.length) before allocated id ambient types live regions pending world created
        obtain ⟨writes, buildTrace, onlyWrites⟩ := buildExpr_byteOwner_fresh_events fuel config environment bytes origin before allocated
          frame before.construction.storage.size 0 direct rfl opened allocatedWorld.ownership.source.structural.1.1.1 current
        cases constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated with
        | stop reason built =>
          have constructed' := constructed
          dsimp only [id] at constructed'
          simp only [constructed', Goose.Proofs.Exit.stepState] at buildTrace
          refine ⟨.begin id :: writes, ?_, ?_⟩
          · simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created', constructed',
              Goose.Proofs.Exit.stepState]
            rw [buildTrace, allocatedEvents]
            simp [List.append_assoc]
          · intro event member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · rfl
            · obtain ⟨index, rfl⟩ := onlyWrites event member
              rfl
        | escape target carriers built =>
          have localAction := buildExpr_byteOwner_local fuel config environment id (.varr (.int .u8)) bytes origin allocated
          rw [constructed] at localAction
          cases localAction
        | jump target kind built =>
          have localAction := buildExpr_byteOwner_local fuel config environment id (.varr (.int .u8)) bytes origin allocated
          rw [constructed] at localAction
          cases localAction
        | ok value built =>
          cases value
          have constructed' := constructed
          dsimp only [id] at constructed'
          simp only [constructed', Goose.Proofs.Exit.stepState] at buildTrace
          obtain ⟨builtFrame, builtDirect⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes origin before allocated built
            frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
          have currentBuilt := frame.same_current builtFrame id current
          have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length before allocated id created
          obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, builtBacking, builtUse, builtProgress, _⟩ :=
            buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 allocated built ready
              (by rw [readySame]; exact packed) (by rw [readySame]; exact request) (by simpa using fits)
              allocatedWorld.ownership.source.structural.1.1.1 current constructed
          have builtBacking' : builtRow.backing = .direct before.construction.storage.size := by
            rw [builtBacking, readySame]; exact direct
          have builtUse' : builtRow.use = .receiver := by rw [builtUse, readySame]; exact receiver
          have stored' : built.construction.storage[before.construction.storage.size]? = some storage := by
            simpa only [PendingDestination.storage, builtBacking', DestinationBacking.writeStorage] using stored
          have completed : completedReceivingDestination id built = .ok id built := by
            simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentBuilt, bind,
              completedDestination, getDestination, EvalM.get, builtPresent, builtProgress, pure]
          obtain ⟨publication, publishTrace, onlyPublish⟩ := publishCompleted_direct_events origin id bytes.length
            before.construction.storage.size built builtRow builtPresent (by simpa using builtProgress) builtUse' builtBacking' storage stored'
          have completed' := completed
          dsimp only [id] at completed'
          cases published : publishCarriers origin [.completed id] built with
          | stop reason after =>
            have published' := published
            dsimp only [id] at published'
            simp only [published, Goose.Proofs.Exit.stepState] at publishTrace
            refine ⟨.begin id :: (writes ++ publication), ?_, ?_⟩
            · simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created', constructed',
                completed', published', Goose.Proofs.Exit.stepState]
              rw [publishTrace, buildTrace, allocatedEvents]
              simp [List.append_assoc]
            · intro event member
              simp only [List.mem_cons, List.mem_append] at member
              rcases member with rfl | member | member
              · rfl
              · obtain ⟨index, rfl⟩ := onlyWrites event member; rfl
              · have same := onlyPublish event member; subst event; rfl
          | escape target carriers after =>
            have localAction := publishCompleted_local origin id built
            rw [published] at localAction
            cases localAction
          | jump target kind after =>
            have localAction := publishCompleted_local origin id built
            rw [published] at localAction
            cases localAction
          | ok value after =>
            cases value
            have published' := published
            dsimp only [id] at published'
            simp only [published, Goose.Proofs.Exit.stepState] at publishTrace
            have sampled := carrierValue_completed_events id after
            refine ⟨.begin id :: (writes ++ publication), ?_, ?_⟩
            · simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created', constructed',
                completed', published', pure, bind]
              rw [sampled, publishTrace, buildTrace, allocatedEvents]
              simp [List.append_assoc]
            · intro event member
              simp only [List.mem_cons, List.mem_append] at member
              rcases member with rfl | member | member
              · rfl
              · obtain ⟨index, rfl⟩ := onlyWrites event member; rfl
              · have same := onlyPublish event member; subst event; rfl

#print axioms evalValue_byteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
