import Goose.Proofs.ConstructionRepresentationBackingBoundary

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct
open Goose.Core (RootInst)

structure SampledRunBacking (layout : LayoutEnv) (bytes : ByteArray) (run : SampledRun) : Prop where
  interval : ∃ fuel finish, elementsEnd fuel layout run.element run.count bytes run.byteStart = .ok finish ∧
    run.byteStart ≤ finish ∧ finish ≤ bytes.size

def storedWrittenRun (stored : StoredValue) (run : SampledRun) : SampledRun :=
  { run with count := match stored.ty with | .limited _ _ => stored.writtenCount | _ => run.count }

inductive StoredValueBacking (layout : LayoutEnv) (state : ExecutionState) (stored : StoredValue) : Prop
  | detached (storage : ReceivingStorage) (element : Ty)
      (present : state.construction.storage[stored.storage]? = some storage)
      (detached : stored.destination = none)
      (type : elementType stored.ty = some element)
      (interval : SampledRunBacking layout storage.bytes (storedWrittenRun stored
        ⟨stored.start + (match stored.ty with | .varr _ => 4 | _ => 0), stored.count, element⟩)) :
      StoredValueBacking layout state stored
  | named (id : Nat) (storage : ReceivingStorage) (destination : PendingDestination) (count : Nat)
      (present : state.construction.storage[stored.storage]? = some storage)
      (named : stored.destination = some id)
      (binding : state.construction.destinations[id]? = some destination)
      (backing : stored.storage = match destination.progress with
        | .published _ => destination.backing.receiverStorage | _ => destination.storage)
      (type : stored.ty = destination.capability.logicalType)
      (start : stored.start = destination.capability.start)
      (progress : progressCount destination.progress = some count)
      (element : Ty) (elementType : Goose.Construct.elementType stored.ty = some element)
      (interval : SampledRunBacking layout storage.bytes (storedWrittenRun stored
        ⟨stored.start + (if destination.layout == .packed && destination.capability.request == .value then 4 else 0),
          (match destination.progress with | .published _ => storage.publishedCount | _ => count), element⟩)) :
      StoredValueBacking layout state stored

inductive ValueStorageBacked (layout : LayoutEnv) (state : ExecutionState) : Value → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : ValueStorageBacked layout state (.int ty value)
  | boolean (value : Bool) : ValueStorageBacked layout state (.bool value)
  | unit : ValueStorageBacked layout state .unit
  | reference (location : Goose.Core.Loc) : ValueStorageBacked layout state (.ref location)
  | slice (location : Goose.Core.Loc) (start count : Nat) : ValueStorageBacked layout state (.slice location start count)
  | array (values : Array Value) (children : ∀ value ∈ values.toList, ValueStorageBacked layout state value) :
      ValueStorageBacked layout state (.fixed values)
  | record (id : Nat) (values : Array Value) (children : ∀ value ∈ values.toList, ValueStorageBacked layout state value) :
      ValueStorageBacked layout state (.record id values)
  | stored (value : StoredValue) (backing : StoredValueBacking layout state value) :
      ValueStorageBacked layout state (.stored value)

structure RootedBackingState (layout : LayoutEnv) (state : ExecutionState) (retainedRoot : RootInst → Prop) : Prop where
  values : ∀ root, retainedRoot root → ∀ value, state.objects.lookup root = some value → ValueStorageBacked layout state value
  identities : ∀ root, retainedRoot root → ∀ stored, state.objects.lookup root = some (.stored stored) →
    state.objectOrdinals.lookup root = some (stored.object.getD stored.storage)

structure AcceptedBackedInput (config : EvalConfig) (typing : TypingEnv) (environment : RuntimeActivation)
    (initialized : Nat) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (retainedRoot : RootInst → Prop) : Prop where
  represented : AcceptedRepresentationInput config typing environment initialized state ambient
  backing : RootedBackingState config.layout state retainedRoot

theorem initial_rootedBackingState (layout : LayoutEnv) (retainedRoot : RootInst → Prop) :
    RootedBackingState layout .initial retainedRoot := by
  constructor <;> intro root outside value present <;> cases present

theorem initial_acceptedBackedInput (config : EvalConfig) (accepted : validate config.module = .ok ())
    (retainedRoot : RootInst → Prop) :
    AcceptedBackedInput config
      ⟨config.module, none, #[], [], 0, 0, .ordinary, .value, [], none, 0⟩
      ⟨0, 0, #[], [], []⟩ 0 .initial [] retainedRoot :=
  ⟨initial_acceptedRepresentationInput config accepted, initial_rootedBackingState config.layout retainedRoot⟩

theorem StoredValueBacking.sampled (layout : LayoutEnv) (state : ExecutionState) (stored : StoredValue)
    (backed : StoredValueBacking layout state stored) :
    ∃ storage run, state.construction.storage[stored.storage]? = some storage ∧
      sampledStored stored state = .ok (storage.bytes, run) state ∧
      SampledRunBacking layout storage.bytes (storedWrittenRun stored run) := by
  cases backed with
  | detached storage element present detached type interval =>
      refine ⟨storage, _, present, ?_, interval⟩
      simp only [sampledStored, getStorage, EvalM.get, bind, present, pure, detached, type]
      rfl
  | named id storage destination count present named binding backing type start progress element elementType interval =>
      refine ⟨storage, _, present, ?_, interval⟩
      cases current : destination.progress <;>
        simp_all only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
          progressCount, Option.some.injEq]

theorem StoredValueBacking.construction_frame {layout : LayoutEnv} {before after : ExecutionState}
    {stored : StoredValue} (same : after.construction = before.construction)
    (valid : StoredValueBacking layout before stored) : StoredValueBacking layout after stored := by
  cases valid with
  | detached storage element present detached type interval =>
      exact .detached storage element (by rw [same]; exact present) detached type interval
  | named id storage destination count present named binding backing type start progress element elementType interval =>
      exact .named id storage destination count (by rw [same]; exact present) named
        (by rw [same]; exact binding) backing type start progress element elementType interval

theorem ValueStorageBacked.construction_frame {layout : LayoutEnv} {before after : ExecutionState}
    {value : Value} (same : after.construction = before.construction)
    (valid : ValueStorageBacked layout before value) : ValueStorageBacked layout after value := by
  induction valid with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values (fun value member => ih value member)
  | record id values children ih => exact .record id values (fun value member => ih value member)
  | stored value backing => exact .stored value (backing.construction_frame same)

private theorem lookup_rebound {α : Type} (entries : List (RootInst × α))
    (root other : RootInst) (value : α) (different : other ≠ root) :
    ((root, value) :: entries.filter (fun entry => entry.1 != root)).lookup other = entries.lookup other := by
  have mismatched : (other == root) = false := beq_eq_false_iff_ne.mpr different
  simp only [List.lookup, mismatched]
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, item⟩
      by_cases same : key = root
      · subst key
        simp only [List.filter, bne_self_eq_false, List.lookup, mismatched]
        exact ih
      · have retained : (key != root) = true := by simpa using same
        by_cases selected : other = key
        · subst key
          simp only [List.filter, retained, List.lookup, beq_self_eq_true]
        · have skipped : (other == key) = false := beq_eq_false_iff_ne.mpr selected
          simpa only [List.filter, retained, List.lookup, skipped] using ih

theorem bindRoot_freshStored_backing (layout : LayoutEnv) (before : ExecutionState)
    (retainedRoot : RootInst → Prop) (root : RootInst) (stored : StoredValue)
    (previous : RootedBackingState layout before retainedRoot)
    (backed : StoredValueBacking layout before stored)
    (fresh : before.objectOrdinals.lookup root = none) :
    ∃ after, bindRoot root (.stored stored) before = .ok () after ∧
      RootedBackingState layout after (fun other => other = root ∨ retainedRoot other) ∧
      after.construction = before.construction := by
  let after := { before with
    objects := (root, .stored stored) :: before.objects.filter (fun entry => entry.1 != root)
    objectOrdinals := (root, stored.object.getD stored.storage) :: before.objectOrdinals.filter (fun entry => entry.1 != root) }
  refine ⟨after, ?_, ?_, rfl⟩
  · simp [bindRoot, fresh, setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
  · constructor
    · intro other retained value present
      by_cases same : other = root
      · subst other
        have valueSame : value = .stored stored := by simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using present.symm
        subst value
        exact .stored stored (StoredValueBacking.construction_frame (before := before) (after := after) rfl backed)
      · have outside : retainedRoot other := retained.resolve_left same
        have original : before.objects.lookup other = some value := by
          dsimp only [after] at present
          rw [lookup_rebound before.objects root other (.stored stored) same] at present
          exact present
        exact ValueStorageBacked.construction_frame (before := before) (after := after) rfl (previous.values other outside value original)
    · intro other retained value present
      by_cases same : other = root
      · subst other
        have valueSame : value = stored := by simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq, Value.stored.injEq] using present.symm
        subst value
        simp only [after, List.lookup, beq_self_eq_true]
      · have outside : retainedRoot other := retained.resolve_left same
        have original : before.objects.lookup other = some (.stored value) := by
          dsimp only [after] at present
          rw [lookup_rebound before.objects root other (.stored stored) same] at present
          exact present
        dsimp only [after]
        rw [lookup_rebound before.objectOrdinals root other (stored.object.getD stored.storage) same]
        exact previous.identities other outside value original

theorem evalValue_rootedOwnerLength (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (retainedRoot : RootInst → Prop) (id : Nat) (root : RootInst) (stored : StoredValue)
    (backing : RootedBackingState config.layout state retainedRoot)
    (outside : retainedRoot root) (resolved : rootOf environment id state = .ok root state)
    (present : state.objects.lookup root = some (.stored stored)) :
    ∃ count, evalValue (fuel + 4) config environment (.len (.of (.var id))) state =
      .ok (.int .i64 count) state := by
  have backed := backing.values root outside (.stored stored) present
  cases backed with
  | stored value backed =>
      obtain ⟨storage, run, found, sampled, interval⟩ := backed.sampled config.layout state stored
      refine ⟨run.count, ?_⟩
      simp only [evalValue, evalView, evalPlace, resolved, bind, pure, readLoc, EvalM.get, present,
        readValuePath, arrayLength, sampled]

end Goose.Proofs.ConstructionRepresentation
