import Goose.Proofs.ExitExecutionRootedPrefixReads
import Goose.Proofs.ExitExecutionStoredChildBacking
import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

def ValuePrefixObservable (layout : LayoutEnv) (before after : ExecutionState)
    (limit : Nat → Nat) (value : Value) : Prop :=
  ∀ stored, StoredOccurrence value stored →
    StoredBackingObservation layout before limit stored ∧
      StoredBackingPrefixFrame before after limit stored

private theorem exceptMapM_member {α β ε : Type} (items : List α) (action : α → Except ε β)
    (values : List β) (evaluated : items.mapM action = .ok values) :
    ∀ value ∈ values, ∃ item, item ∈ items ∧ action item = .ok value := by
  induction items generalizing values with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at evaluated; subst values; simp
  | cons item items ih =>
    cases first : action item with
    | error reason => simp only [List.mapM_cons, first, bind, Except.bind] at evaluated; cases evaluated
    | ok head =>
      cases rest : items.mapM action with
      | error reason => simp only [List.mapM_cons, first, rest, bind, Except.bind] at evaluated; cases evaluated
      | ok tail =>
        have same : head :: tail = values := by
          simpa only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using evaluated
        subst values
        intro value member
        rcases List.mem_cons.mp member with same | remaining
        · subst value; exact ⟨item, by simp, first⟩
        · obtain ⟨selected, present, found⟩ := ih tail rest value remaining
          exact ⟨selected, List.mem_cons_of_mem _ present, found⟩

theorem fixedValue_no_storedOccurrence (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start : Nat) (value : Value)
    (decoded : fixedValue fuel layout ty bytes start = .ok value) :
    ∀ stored, ¬StoredOccurrence value stored := by
  induction fuel generalizing ty start value with
  | zero => cases decoded
  | succ fuel ih =>
    cases ty with
    | int ty =>
      cases integer : bytesInt ty bytes start <;>
        simp only [fixedValue, integer, bind, Except.bind, Except.mapError, pure, Except.pure] at decoded
      · cases decoded
      · cases decoded; intro stored occurrence; cases occurrence
    | bool =>
      cases found : bytes.data[start]? <;> simp only [fixedValue, found, pure, Except.pure] at decoded
      · cases decoded
      · cases decoded; intro stored occurrence; cases occurrence
    | arr element count =>
      cases sized : fixedByteSize? layout element with
      | none => simp only [fixedValue, sized] at decoded; cases decoded
      | some width =>
        cases elements : (List.range count).mapM
            (fun index => fixedValue fuel layout element bytes (start + index * width)) with
        | error reason => simp only [fixedValue, sized, elements, bind, Except.bind] at decoded; cases decoded
        | ok values =>
          simp only [fixedValue, sized, elements, bind, Except.bind, pure, Except.pure] at decoded
          cases decoded
          intro stored occurrence
          cases occurrence with
          | array _ child _ member occurrence =>
            obtain ⟨index, present, found⟩ := exceptMapM_member _ _ _ elements child (by simpa using member)
            exact ih element _ child found stored occurrence
    | structT id members =>
      cases descriptor : layout.structs[id]? with
      | none => simp only [fixedValue, descriptor] at decoded; cases decoded
      | some definition =>
        cases fields : definition.fields.toList.mapM
            (fun field => fixedValue fuel layout field.ty bytes (start + field.byteOffset)) with
        | error reason => simp only [fixedValue, descriptor, fields, bind, Except.bind] at decoded; cases decoded
        | ok values =>
          simp only [fixedValue, descriptor, fields, bind, Except.bind, pure, Except.pure] at decoded
          cases decoded
          intro stored occurrence
          cases occurrence with
          | record _ _ child _ member occurrence =>
            obtain ⟨field, present, found⟩ := exceptMapM_member _ _ _ fields child (by simpa using member)
            exact ih field.ty _ child found stored occurrence
    | _ => cases decoded

theorem valuePrefixObservable_stored_child (fuel : Nat) (layout : LayoutEnv)
    (before after : ExecutionState) (limit : Nat → Nat) (stored : StoredValue)
    (index : Nat) (value : Value)
    (observable : ValuePrefixObservable layout before after limit (.stored stored))
    (read : readStoredElement fuel layout stored index before = .ok value before) :
    ValuePrefixObservable layout before after limit value := by
  obtain ⟨observed, frame⟩ := observable stored (.stored stored)
  obtain ⟨storage, sampledRun, backingFuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  obtain ⟨original, current, originalFound, currentFound, bytes, published⟩ := frame.storage
  have same := Option.some.inj (originalFound.symm.trans present)
  subst original
  let run := storedWrittenRun stored sampledRun
  have originalRun : storedPathRun stored before = .ok (storage.bytes, run) before := by
    simp only [storedPathRun, sampled, bind, pure]
    rfl
  simp only [readStoredElement, originalRun, bind] at read
  cases interval : elementInterval fuel layout storage.bytes run index with
  | error reason =>
    cases reason <;> simp only [interval, liftLayout, fault, timeout, EvalM.stop] at read <;> cases read
  | ok pair =>
    obtain ⟨start, last⟩ := pair
    have within := elementInterval_within_run fuel backingFuel layout storage.bytes run index start last finish interval measured
    have scanned := (elementInterval_result_inv fuel layout storage.bytes run index start last interval).2.2
    simp only [interval, liftLayout, pure] at read
    cases nonfixed : run.element.nonfixed with
    | false =>
      simp only [nonfixed, Bool.false_eq_true, ↓reduceIte] at read
      cases decoded : fixedValue fuel layout run.element storage.bytes start with
      | error reason => simp only [decoded, Goose.Construct.liftExcept, EvalM.stop] at read; cases read
      | ok child =>
        simp only [decoded, Goose.Construct.liftExcept, pure] at read
        cases read
        intro observed occurrence
        exact False.elim (fixedValue_no_storedOccurrence fuel layout run.element storage.bytes start value decoded observed occurrence)
    | true =>
      simp only [nonfixed, ↓reduceIte] at read
      cases packed : samplePacked run.element storage.bytes start with
      | error reason =>
        cases reason <;> simp only [packed, fault, timeout, EvalM.stop] at read <;> cases read
      | ok packedRun =>
        simp only [packed] at read
        cases read
        intro child occurrence
        cases occurrence
        let detached : StoredValue := ⟨stored.storage, start, run.element, packedRun.count, none,
          some (stored.object.getD stored.storage), stored.path ++ [index], packedRun.count⟩
        obtain ⟨childFuel, childBacking⟩ := packedEnd_sampled_run_backing fuel layout run.element
          storage.bytes start last packedRun nonfixed scanned packed
        have normalizedCount : (storedWrittenRun detached packedRun).count = packedRun.count := by
          dsimp only [storedWrittenRun, detached]
          split <;> rfl
        have sampledChild := sampledStored_detached_of_samplePacked before stored.storage storage start
          run.element packedRun (some (stored.object.getD stored.storage)) (stored.path ++ [index]) present packed
        refine ⟨?_, ?_⟩
        · refine ⟨storage, packedRun, childFuel, last, present, sampledChild, ?_, ?_, ?_⟩
          · change elementsEnd childFuel layout packedRun.element (storedWrittenRun detached packedRun).count
              storage.bytes packedRun.byteStart = .ok last
            rw [normalizedCount]
            exact childBacking
          · exact elementsEnd_monotone childFuel layout packedRun.element packedRun.count storage.bytes packedRun.byteStart last childBacking
          · change last ≤ limit stored.storage
            omega
        · refine ⟨⟨storage, current, present, currentFound, bytes, published⟩, ?_⟩
          intro id absent
          cases absent

private theorem query_bind_observation (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (query : StateQuery action)
    (observed : mapStepState (fun _ => ExecutionState.initial) (action after) =
      mapStepState (fun _ => ExecutionState.initial) (action before))
    (continued : ∀ value, action before = .ok value before →
      mapStepState (fun _ => ExecutionState.initial) (next value after) =
        mapStepState (fun _ => ExecutionState.initial) (next value before)) :
    mapStepState (fun _ => ExecutionState.initial) ((action >>= next) after) =
      mapStepState (fun _ => ExecutionState.initial) ((action >>= next) before) := by
  have beforeState := query before
  have afterState := query after
  cases left : action before <;> cases right : action after
  all_goals simp only [left, right, Goose.Proofs.Exit.stepState] at beforeState afterState
  all_goals subst_vars
  all_goals simp only [left, right, mapStepState] at observed
  all_goals try cases observed
  all_goals simp only [bind, left, right]
  all_goals first | rfl | exact continued _ left

theorem readValuePath_prefix_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState) (limit : Nat → Nat)
    (value : Value) (path : List Nat)
    (observable : ValuePrefixObservable (.ofModule module) before after limit value) :
    mapStepState (fun _ => ExecutionState.initial)
        (readValuePath fuel (.ofModule module) value path after) =
      mapStepState (fun _ => ExecutionState.initial)
        (readValuePath fuel (.ofModule module) value path before) := by
  induction fuel generalizing value path with
  | zero => rfl
  | succ fuel ih =>
    cases path with
    | nil => rfl
    | cons index rest =>
      cases value with
      | int ty value => rfl
      | bool value => rfl
      | unit => rfl
      | ref location => rfl
      | slice location start count => rfl
      | fixed elements =>
        cases found : elements[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind, mapStepState]
        | some child =>
          simp only [readValuePath, found, pure, bind]
          apply ih child rest
          intro stored occurrence
          exact observable stored (.array elements child stored (by simpa using Array.mem_of_getElem? found) occurrence)
      | record id fields =>
        cases found : fields[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind, mapStepState]
        | some child =>
          simp only [readValuePath, found, pure, bind]
          apply ih child rest
          intro stored occurrence
          exact observable stored (.record id fields child stored (by simpa using Array.mem_of_getElem? found) occurrence)
      | stored stored =>
        simp only [readValuePath]
        apply query_bind_observation _ _ before after (stateQuery_readStoredElement fuel (.ofModule module) stored index)
        · obtain ⟨observed, frame⟩ := observable stored (.stored stored)
          exact storedBackingObservation_readStoredElement_observation fuel module accepted before after limit stored index observed frame
        · intro child read
          apply ih child rest
          exact valuePrefixObservable_stored_child fuel (.ofModule module) before after limit stored index child observable read

theorem readLoc_prefix_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState) (limit : Nat → Nat)
    (location : Goose.Core.Loc)
    (root : after.objects.lookup location.root = before.objects.lookup location.root)
    (observable : ∀ value, before.objects.lookup location.root = some value →
      ValuePrefixObservable (.ofModule module) before after limit value) :
    mapStepState (fun _ => ExecutionState.initial)
        (readLoc fuel (.ofModule module) location after) =
      mapStepState (fun _ => ExecutionState.initial)
        (readLoc fuel (.ofModule module) location before) := by
  cases found : before.objects.lookup location.root with
  | none => simp only [readLoc, EvalM.get, bind, root, found, fault, EvalM.stop, mapStepState]
  | some value =>
    simp only [readLoc, EvalM.get, bind, root, found]
    exact readValuePath_prefix_observation fuel module accepted before after limit value location.path (observable value found)

theorem rootedBackingObservations_readLoc_observation (fuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState)
    (retainedRoot : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations (.ofModule module) before retainedRoot limit)
    (frame : RootedBackingPrefixFrame before after retainedRoot limit)
    (location : Goose.Core.Loc) (retained : retainedRoot location.root) :
    mapStepState (fun _ => ExecutionState.initial)
        (readLoc fuel (.ofModule module) location after) =
      mapStepState (fun _ => ExecutionState.initial)
        (readLoc fuel (.ofModule module) location before) := by
  apply readLoc_prefix_observation fuel module accepted before after limit location (frame.objects location.root retained)
  intro value found stored occurrence
  exact ⟨valid.observations location.root retained value found stored occurrence,
    frame.sources location.root retained value found stored occurrence⟩

#print axioms fixedValue_no_storedOccurrence
#print axioms valuePrefixObservable_stored_child
#print axioms readValuePath_prefix_observation
#print axioms readLoc_prefix_observation
#print axioms rootedBackingObservations_readLoc_observation

end Goose.Proofs.ExitExecution
