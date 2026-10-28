import Goose.Proofs.ConstructionByteWriteStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

local syntax "allocation_stop_split " ident : tactic
elab_rules : tactic
  | `(tactic| allocation_stop_split $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no allocation condition"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1200000 in
theorem openDestination_packed_fault_unchanged_any (state final : ConstructionState) (target : Nat) (knownCount : Option Nat)
    (capability : Goose.Core.Destination Ty) (reason : ConstructionFault)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed knownCount state = .fault reason final) :
    final = state := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases found : state.storage[target]? with
  | none => simp only [found, ConstructionResult.fault.injEq] at executed; exact executed.2.symm
  | some storage =>
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    cases knownCount <;>
    repeat' first
      | contradiction
      | simp_all only [ConstructionM.get, ConstructionM.set, ConstructionM.fail, available_result,
          replaceStorage_result, emit_result, hasPrefix_result, pure,
          ConstructionResult.fault.injEq, PendingDestination.storage,
          DestinationBacking.writeStorage, DestinationBacking.receiverStorage,
          Nat.lt_irrefl, ↓reduceIte, reduceCtorEq,
          beq_self_eq_true, Bool.and_true, Bool.false_eq_true]
      | allocation_stop_split executed
      | split at executed
      | rcases executed with ⟨rfl, rfl⟩
    all_goals assumption


set_option maxHeartbeats 1200000 in
theorem openDestination_packed_fault_unchanged (state final : ConstructionState) (target count : Nat)
    (capability : Goose.Core.Destination Ty) (reason : ConstructionFault)
    (request : capability.request = .value)
    (executed : openDestination target capability .packed (some count) state = .fault reason final) :
    final = state := by
  exact openDestination_packed_fault_unchanged_any state final target (some count) capability reason request executed

theorem newDestination_byteOwner_stopped_state_any (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none knownCount before = .stop stop after) :
    after = { before with construction :=
      { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } } := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout (.varr (.int .u8)) >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩ selected knownCount))
      prepared) = .stop stop after at executed
  simp only [receivingLayout, pure, bind, liftConstruction] at executed
  cases opened : openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, owner⟩
      .packed knownCount prepared.construction with
  | ok value final => simp only [opened] at executed; cases executed
  | fault reason final =>
    have unchanged := openDestination_packed_fault_unchanged_any prepared.construction final
      before.construction.storage.size knownCount _ reason rfl opened
    subst final
    cases reason <;> simp only [opened, ExecutionStep.stop.injEq] at executed <;>
      obtain ⟨_, same⟩ := executed <;> exact same.symm


theorem newDestination_byteOwner_stopped_state (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before = .stop stop after) :
    after = { before with construction :=
      { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } } := by
  exact newDestination_byteOwner_stopped_state_any layout owner origin (some count) before after stop executed

theorem newDestination_byteOwner_stopped_source (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (origin : Goose.Core.OriginId) (count : Nat) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (valid : OwnershipSourceState before.construction)
    (executed : newDestination layout owner (.varr (.int .u8)) .value origin none (some count) before = .stop stop after) :
    OwnershipSourceState after.construction ∧ after.construction.destinations = before.construction.destinations := by
  have same := newDestination_byteOwner_stopped_state layout owner origin count before after stop executed
  subst after
  have preserved := constructionPrimitive_sourceState_of_sourceExtension (reserveStorage ByteArray.empty 0)
    (.reserveStorage ByteArray.empty 0) before.construction valid
    (reserveStorage_ownership_source ByteArray.empty 0 before.construction)
  exact ⟨by simpa only [reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure,
    ConstructionResult.finalState] using preserved, rfl⟩

theorem newDestination_byteOwner_stopped_frame_any {config : EvalConfig} {accepted : AcceptedModule config}
    {source : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (owner : Goose.Core.ActId) (origin : Goose.Core.OriginId) (knownCount : Option Nat) (stop : Goose.Core.Stop)
    (valid : AcceptedFrame config accepted source before types)
    (executed : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .stop stop after) :
    AcceptedFrame config accepted source after types := by
  have same := newDestination_byteOwner_stopped_state_any config.layout owner origin knownCount before after stop executed
  have objects := congrArg ExecutionState.objects same
  have ordinals := congrArg ExecutionState.objectOrdinals same
  have acts := congrArg ExecutionState.nextAct same
  have scopes := congrArg ExecutionState.nextScope same
  refine ⟨valid.compatible, ?_, ?_, valid.initializingBefore, valid.aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [acts] using valid.frontier
  · simpa only [scopes] using valid.scopeFrontier
  · intro var member
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := valid.locals var member
    exact ⟨descriptor, root, value, declared, rootOf_transfer source.interpretation var before after root resolved,
      by rw [objects]; exact found, represented⟩
  · intro var member descriptor root declared resolved
    exact valid.localTypes var member descriptor root declared
      (rootOf_transfer source.interpretation var after before root resolved)
  · intro var uninitialized root resolved
    obtain ⟨absent, ordinal⟩ := valid.uninitializedLocals var uninitialized root
      (rootOf_transfer source.interpretation var after before root resolved)
    exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
  · intro var uninitialized root resolved
    exact valid.uninitializedTypes var uninitialized root
      (rootOf_transfer source.interpretation var after before root resolved)
  · intro global future within
    obtain ⟨absent, ordinal⟩ := valid.futureGlobals global future within
    exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
  · intro var member root value resolved found
    exact valid.direct var member root value (rootOf_transfer source.interpretation var after before root resolved)
      (by rw [objects] at found; exact found)
  · intro fuel var member roots annotated root location value resolved found read interior reference
    have prior := rootOf_transfer source.interpretation var after before root resolved
    have oldFound : before.objects.lookup root = some (.ref location) := by rw [objects] at found; exact found
    have priorRead := readLoc_directReference_transfer fuel config.layout location after before value interior
      (by rw [objects]) read reference
    exact valid.contents fuel var member roots annotated root location value prior oldFound priorRead interior reference


theorem newDestination_byteOwner_stopped_frame {config : EvalConfig} {accepted : AcceptedModule config}
    {source : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (owner : Goose.Core.ActId) (origin : Goose.Core.OriginId) (count : Nat) (stop : Goose.Core.Stop)
    (valid : AcceptedFrame config accepted source before types)
    (executed : newDestination config.layout owner (.varr (.int .u8)) .value origin none (some count) before = .stop stop after) :
    AcceptedFrame config accepted source after types := by
  exact newDestination_byteOwner_stopped_frame_any owner origin (some count) stop valid executed

#print axioms newDestination_byteOwner_stopped_frame
#print axioms newDestination_byteOwner_stopped_frame_any
#print axioms newDestination_byteOwner_stopped_source
#print axioms openDestination_packed_fault_unchanged
#print axioms openDestination_packed_fault_unchanged_any
#print axioms newDestination_byteOwner_stopped_state
#print axioms newDestination_byteOwner_stopped_state_any
end Goose.Proofs.ConstructionAcceptedExecution
