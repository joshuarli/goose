import Goose.Proofs.ExitExecutionCleanupStorageObservations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

inductive OutsideReadResult (before after : ExecutionState) :
    ExecutionStep α → ExecutionStep α → Prop
  | ok (value : α) : OutsideReadResult before after (.ok value before) (.ok value after)
  | stop (reason : Stop) : OutsideReadResult before after (.stop reason before) (.stop reason after)

def OutsideReadFrame (before after : ExecutionState) (action : EvalM α) : Prop :=
  OutsideReadResult before after (action before) (action after)

private theorem read_bind (before after : ExecutionState) (action : EvalM α) (next : α → EvalM β)
    (first : OutsideReadFrame before after action)
    (rest : ∀ value, OutsideReadFrame before after (next value)) :
    OutsideReadFrame before after (action >>= next) := by
  unfold OutsideReadFrame at first ⊢
  generalize left : action before = lhs at first
  generalize right : action after = rhs at first
  cases first with
  | ok value => simpa only [OutsideReadFrame, bind, left, right] using rest value
  | stop reason =>
      simp only [bind, left, right]
      exact .stop reason

private theorem read_pure (before after : ExecutionState) (value : α) :
    OutsideReadFrame before after (pure value) := .ok value

private theorem read_fault (before after : ExecutionState) (kind : FaultKind) :
    OutsideReadFrame before after (Goose.Construct.fault kind : EvalM α) := .stop (.fault kind)

private theorem read_except (before after : ExecutionState) (result : Except Stop α) :
    OutsideReadFrame before after (Goose.Construct.liftExcept result) := by
  cases result with
  | ok value => exact .ok value
  | error reason => exact .stop reason

private theorem read_layout (before after : ExecutionState) (result : Except LayoutFault α) :
    OutsideReadFrame before after (liftLayout result) := by
  cases result with
  | ok value => exact .ok value
  | error reason => cases reason <;> constructor

inductive ValueReadBackings (storageAllowed : StorageId → Prop)
    (destinationAllowed : DestinationId → Prop) : Value → Prop
  | int (ty : IntTy) (value : Int) : ValueReadBackings storageAllowed destinationAllowed (.int ty value)
  | bool (value : Bool) : ValueReadBackings storageAllowed destinationAllowed (.bool value)
  | unit : ValueReadBackings storageAllowed destinationAllowed .unit
  | ref (location : Loc) : ValueReadBackings storageAllowed destinationAllowed (.ref location)
  | slice (location : Loc) (start count : Nat) :
      ValueReadBackings storageAllowed destinationAllowed (.slice location start count)
  | fixed (elements : Array Value)
      (children : ∀ (index : Nat) (child : Value), elements[index]? = some child →
        ValueReadBackings storageAllowed destinationAllowed child) :
      ValueReadBackings storageAllowed destinationAllowed (.fixed elements)
  | record (id : StructId) (fields : Array Value)
      (children : ∀ (index : Nat) (child : Value), fields[index]? = some child →
        ValueReadBackings storageAllowed destinationAllowed child) :
      ValueReadBackings storageAllowed destinationAllowed (.record id fields)
  | stored (value : StoredValue) (storage : storageAllowed value.storage)
      (destination : ∀ id, value.destination = some id → destinationAllowed id) :
      ValueReadBackings storageAllowed destinationAllowed (.stored value)

abbrev OutsideValueReads (before after : ExecutionState) :=
  ValueReadBackings
    (fun id => after.construction.storage[id]? = before.construction.storage[id]?)
    (fun id => after.construction.destinations[id]? = before.construction.destinations[id]?)

private theorem read_storage (before after : ExecutionState) (id : StorageId)
    (same : after.construction.storage[id]? = before.construction.storage[id]?) :
    OutsideReadFrame before after (getStorage id) := by
  cases found : before.construction.storage[id]? with
  | none => simpa only [OutsideReadFrame, getStorage, EvalM.get, bind, found, same,
      Goose.Construct.fault, EvalM.stop] using (OutsideReadResult.stop (before := before) (after := after) (.fault .danglingRoot) : OutsideReadResult before after (.stop (.fault .danglingRoot) before : ExecutionStep ReceivingStorage) (.stop (.fault .danglingRoot) after))
  | some value => simpa only [OutsideReadFrame, getStorage, EvalM.get, bind, pure, same, found]
      using (OutsideReadResult.ok (before := before) (after := after) value)

private theorem read_destination (before after : ExecutionState) (id : DestinationId)
    (same : after.construction.destinations[id]? = before.construction.destinations[id]?) :
    OutsideReadFrame before after (getDestination id) := by
  cases found : before.construction.destinations[id]? with
  | none => simpa only [OutsideReadFrame, getDestination, EvalM.get, bind, found, same,
      Goose.Construct.fault, EvalM.stop] using (OutsideReadResult.stop (before := before) (after := after) (.fault .unbound) : OutsideReadResult before after (.stop (.fault .unbound) before : ExecutionStep PendingDestination) (.stop (.fault .unbound) after))
  | some value => simpa only [OutsideReadFrame, getDestination, EvalM.get, bind, pure, same, found]
      using (OutsideReadResult.ok (before := before) (after := after) value)

theorem sampledStored_outside_reads (before after : ExecutionState) (stored : StoredValue)
    (storage : after.construction.storage[stored.storage]? = before.construction.storage[stored.storage]?)
    (destination : ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?) :
    OutsideReadFrame before after (sampledStored stored) := by
  cases present : before.construction.storage[stored.storage]? with
  | none =>
      simp only [OutsideReadFrame, sampledStored, getStorage, EvalM.get, bind,
        storage, present, Goose.Construct.fault, EvalM.stop]
      constructor
  | some previous =>
      cases selected : stored.destination with
      | none =>
          cases element : elementType stored.ty <;>
            simp only [OutsideReadFrame, sampledStored, getStorage, EvalM.get, bind, pure,
              storage, present, selected, element, Goose.Construct.fault, EvalM.stop] <;> constructor
      | some id =>
          have same := destination id selected
          cases found : before.construction.destinations[id]? with
          | none =>
              simp only [OutsideReadFrame, sampledStored, getStorage, getDestination, EvalM.get,
                bind, pure, storage, present, selected, same, found, Goose.Construct.fault, EvalM.stop]
              constructor
          | some pending =>
              cases progress : pending.progress <;> cases element : elementType stored.ty <;>
                simp only [OutsideReadFrame, sampledStored, getStorage, getDestination, EvalM.get,
                  bind, pure, storage, present, selected, same, found, progress, element,
                  progressCount, Goose.Construct.fault, EvalM.stop] <;> constructor

private theorem except_mapM_members {α β : Type} (action : α → Except Stop β) (values : List α)
    (property : β → Prop) (valid : ∀ value result, action value = .ok result → property result)
    (results : List β) (normal : values.mapM action = .ok results) :
    ∀ result ∈ results, property result := by
  induction values generalizing results with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at normal
      subst results
      simp
  | cons value values ih =>
      cases first : action value with
      | error reason => simp [List.mapM_cons, bind, Except.bind, first] at normal
      | ok result =>
          cases rest : values.mapM action with
          | error reason => simp [List.mapM_cons, bind, Except.bind, first, rest] at normal
          | ok tail =>
              have same : result :: tail = results := by simpa [List.mapM_cons, bind, pure, Functor.map, Except.bind, Except.pure, Except.map, first, rest] using normal
              subst results
              intro item member
              rcases List.mem_cons.mp member with equal | member
              · subst item
                exact valid value result first
              · exact ih tail rest item member

private theorem fixedValue_outside_reads (fuel : Nat) (layout : LayoutEnv) (ty : Goose.Construct.Ty)
    (bytes : ByteArray) (start : Nat) (before after : ExecutionState)
    (value : Value) (normal : fixedValue fuel layout ty bytes start = .ok value) :
    OutsideValueReads before after value := by
  induction fuel generalizing ty start value with
  | zero => simp [fixedValue] at normal
  | succ fuel ih =>
      cases ty with
      | int ty =>
          cases decoded : bytesInt ty bytes start <;> simp [bind, pure, Except.bind, Except.pure, Except.mapError, fixedValue, decoded] at normal
          subst value
          exact .int _ _
      | bool =>
          cases found : bytes.data[start]? <;> simp [pure, Except.pure, fixedValue, found] at normal
          subst value
          exact .bool _
      | arr element count =>
          cases width : fixedByteSize? layout element with
          | none => simp [fixedValue, width] at normal
          | some size =>
              cases elements : (List.range count).mapM (fun index => fixedValue fuel layout element bytes (start + index * size)) with
              | error reason => simp [bind, Except.bind, fixedValue, width, elements] at normal
              | ok values =>
                  have equal : Value.fixed values.toArray = value := by simpa [bind, pure, Functor.map, Except.bind, Except.pure, Except.map, Except.mapError, fixedValue, width, elements] using normal
                  subst value
                  apply ValueReadBackings.fixed
                  intro index child found
                  apply except_mapM_members _ _ (OutsideValueReads before after) (fun index result proof => ih element _ result proof) values elements child
                  exact List.mem_toArray.mp (Array.mem_of_getElem? found)
      | structT id fields =>
          cases descriptor : layout.structs[id]? with
          | none => simp [fixedValue, descriptor] at normal
          | some descriptorValue =>
              cases elements : descriptorValue.fields.toList.mapM (fun field => fixedValue fuel layout field.ty bytes (start + field.byteOffset)) with
              | error reason => simp [bind, Except.bind, fixedValue, descriptor, elements] at normal
              | ok values =>
                  have equal : Value.record id values.toArray = value := by simpa [bind, pure, Functor.map, Except.bind, Except.pure, Except.map, Except.mapError, fixedValue, descriptor, elements] using normal
                  subst value
                  apply ValueReadBackings.record
                  intro index child found
                  apply except_mapM_members _ _ (OutsideValueReads before after) (fun field result proof => ih field.ty _ result proof) values elements child
                  exact List.mem_toArray.mp (Array.mem_of_getElem? found)
      | _ => simp [fixedValue] at normal

private theorem storedPathRun_outside_reads (before after : ExecutionState) (stored : StoredValue)
    (storage : after.construction.storage[stored.storage]? = before.construction.storage[stored.storage]?)
    (destination : ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?) :
    OutsideReadFrame before after (storedPathRun stored) := by
  exact read_bind _ _ _ _ (sampledStored_outside_reads before after stored storage destination)
    (fun _ => read_pure _ _ _)

theorem readStoredElement_outside_reads (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (stored : StoredValue) (index : Nat)
    (storage : after.construction.storage[stored.storage]? = before.construction.storage[stored.storage]?)
    (destination : ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?) :
    OutsideReadFrame before after (readStoredElement fuel layout stored index) := by
  unfold readStoredElement
  apply read_bind _ _ _ _ (storedPathRun_outside_reads before after stored storage destination)
  intro sample
  apply read_bind _ _ _ _ (read_layout before after _)
  rintro ⟨start, finish⟩
  dsimp only
  split
  · exact read_bind _ _ _ _ (read_layout before after _) (fun _ => read_pure _ _ _)
  · exact read_except _ _ _

private theorem readStoredElement_result_outside (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (stored : StoredValue) (index : Nat)
    (storage : after.construction.storage[stored.storage]? = before.construction.storage[stored.storage]?)
    (value : Value) (state : ExecutionState)
    (normal : readStoredElement fuel layout stored index before = .ok value state) :
    OutsideValueReads before after value := by
  unfold readStoredElement at normal
  cases sample : storedPathRun stored before with
  | ok result current =>
      simp only [sample, bind] at normal
      cases interval : elementInterval fuel layout result.1 result.2 index with
      | error reason => cases reason <;> simp [interval, liftLayout, Goose.Construct.fault, Goose.Construct.timeout, EvalM.stop] at normal
      | ok range =>
          simp only [interval, liftLayout, pure] at normal
          split at normal
          · cases packed : samplePacked result.2.element result.1 range.1 with
            | error reason => cases reason <;> simp [packed, Goose.Construct.fault, Goose.Construct.timeout, EvalM.stop] at normal
            | ok packedRun =>
                simp only [packed, ExecutionStep.ok.injEq] at normal
                rcases normal with ⟨equal, _⟩
                subst value
                exact .stored _ storage (by simp)
          · cases decoded : fixedValue fuel layout result.2.element result.1 range.1 with
            | error reason => simp [decoded, Goose.Construct.liftExcept, EvalM.stop] at normal
            | ok decodedValue =>
                have equal : decodedValue = value := by
                  have pair : decodedValue = value ∧ current = state := by
                    simpa only [decoded, Goose.Construct.liftExcept, pure, ExecutionStep.ok.injEq] using normal
                  exact pair.1
                subst value
                exact fixedValue_outside_reads fuel layout _ _ _ before after decodedValue decoded
  | stop reason current => simp [sample, bind] at normal
  | escape address carriers current => simp [sample, bind] at normal
  | jump target kind current => simp [sample, bind] at normal

private theorem read_bind_ok (before after : ExecutionState) (action : EvalM α) (next : α → EvalM β)
    (first : OutsideReadFrame before after action)
    (rest : ∀ value, action before = .ok value before → OutsideReadFrame before after (next value)) :
    OutsideReadFrame before after (action >>= next) := by
  unfold OutsideReadFrame at first ⊢
  generalize left : action before = lhs at first
  generalize right : action after = rhs at first
  cases first with
  | ok value => simpa only [OutsideReadFrame, bind, left, right] using rest value left
  | stop reason =>
      simp only [bind, left, right]
      exact .stop reason

theorem readValuePath_outside_reads (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (value : Value) (path : List Nat)
    (backings : OutsideValueReads before after value) :
    OutsideReadFrame before after (readValuePath fuel layout value path) := by
  induction fuel generalizing value path with
  | zero => exact .stop .timeout
  | succ fuel ih =>
      cases path with
      | nil => exact .ok value
      | cons index path =>
          cases backings with
          | fixed elements children | record id elements children =>
              cases found : elements[index]? with
              | none => simpa only [OutsideReadFrame, readValuePath, found, Goose.Construct.fault,
                  EvalM.stop, bind] using (OutsideReadResult.stop (before := before) (after := after) (.fault .pathRange) : OutsideReadResult before after (.stop (.fault .pathRange) before : ExecutionStep Value) (.stop (.fault .pathRange) after))
              | some child => simpa only [readValuePath, found, bind, pure] using ih child path (children index child found)
          | stored stored storage destination =>
              apply read_bind_ok _ _ _ _ (readStoredElement_outside_reads fuel layout before after stored index storage destination)
              intro child normal
              exact ih child path (readStoredElement_result_outside fuel layout before after stored index storage child before normal)
          | _ => exact .stop (.fault .shape)

theorem readLoc_outside_reads (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (location : Loc)
    (root : after.objects.lookup location.root = before.objects.lookup location.root)
    (backings : ∀ value, before.objects.lookup location.root = some value → OutsideValueReads before after value) :
    OutsideReadFrame before after (Goose.Construct.readLoc fuel layout location) := by
  cases found : before.objects.lookup location.root with
  | none =>
      simpa only [OutsideReadFrame, Goose.Construct.readLoc, EvalM.get, bind, root, found,
        Goose.Construct.fault, EvalM.stop] using
        (OutsideReadResult.stop (before := before) (after := after) (.fault .danglingRoot) : OutsideReadResult before after (.stop (.fault .danglingRoot) before : ExecutionStep Value) (.stop (.fault .danglingRoot) after))
  | some value =>
      simpa only [OutsideReadFrame, Goose.Construct.readLoc, EvalM.get, bind, root, found] using
        readValuePath_outside_reads fuel layout before after value location.path (backings value found)

theorem OutsideReadResult.observation (before after : ExecutionState)
    (left right : ExecutionStep α) (frame : OutsideReadResult before after left right) :
    mapStepState (fun _ => ExecutionState.initial) right =
      mapStepState (fun _ => ExecutionState.initial) left := by
  cases frame <;> rfl


theorem ValueReadBackings.frame (storageAllowed : StorageId → Prop)
    (destinationAllowed : DestinationId → Prop) (before after : ExecutionState)
    (storages : ∀ id, storageAllowed id → after.construction.storage[id]? = before.construction.storage[id]?)
    (destinations : ∀ id, destinationAllowed id →
      after.construction.destinations[id]? = before.construction.destinations[id]?)
    (value : Value) (backings : ValueReadBackings storageAllowed destinationAllowed value) :
    OutsideValueReads before after value := by
  induction backings with
  | int ty value => exact .int ty value
  | bool value => exact .bool value
  | unit => exact .unit
  | ref location => exact .ref location
  | slice location start count => exact .slice location start count
  | fixed elements children ih => exact .fixed elements ih
  | record id fields children ih => exact .record id fields ih
  | stored stored storage destination =>
      exact .stored stored (storages stored.storage storage) (fun id present => destinations id (destination id present))

theorem readLoc_disjoint_backings (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (location : Loc)
    (changes : List CleanupStorageBoundary) (changedDestinations : List DestinationId)
    (storageTrace : CleanupStorageTrace changes before.construction.storage after.construction.storage)
    (destinationFrame : ∀ id, id ∉ changedDestinations →
      after.construction.destinations[id]? = before.construction.destinations[id]?)
    (root : after.objects.lookup location.root = before.objects.lookup location.root)
    (backings : ∀ value, before.objects.lookup location.root = some value →
      ValueReadBackings (fun id => ∀ change ∈ changes, change.storage ≠ id)
        (fun id => id ∉ changedDestinations) value) :
    OutsideReadFrame before after (Goose.Construct.readLoc fuel layout location) := by
  apply readLoc_outside_reads fuel layout before after location root
  intro value present
  exact (backings value present).frame _ _ before after
    (fun id outside => storageTrace.untouched id outside) destinationFrame value

end Goose.Proofs.ExitExecution
