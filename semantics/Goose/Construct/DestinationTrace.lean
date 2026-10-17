import Goose.Construct.Destination

set_option Elab.async false

namespace Goose.Construct
open Goose.Core

inductive DestinationObservation
  | begin
  | write (index : Nat)
  | stage
  | copy (source : CopySource)
  | relocate (reason : RelocationReason)
  | publish
  | abandon
  deriving DecidableEq, Repr

def observeDestination (id : DestinationId) : ConstructionEvent → Option DestinationObservation
  | .begin target => if target = id then some .begin else none
  | .write target index => if target = id then some (.write index) else none
  | .stage target => if target = id then some .stage else none
  | .copy source target => if target = id then some (.copy source) else none
  | .relocate target reason => if target = id then some (.relocate reason) else none
  | .publish target => if target = id then some .publish else none
  | .abandon target => if target = id then some .abandon else none

def destinationObservations (id : DestinationId) (events : List ConstructionEvent) :
    List DestinationObservation := events.filterMap (observeDestination id)

inductive DestinationTracePhase
  | unseen
  | live (staged wrote : Bool)
  | published
  | abandoned
  deriving DecidableEq, Repr

def destinationTraceStep : DestinationTracePhase → DestinationObservation → Option DestinationTracePhase
  | .unseen, .begin => some (.live false false)
  | .live staged _, .write _ => some (.live staged true)
  | .live false false, .stage => some (.live true false)
  | phase@(.live _ _), .copy _ => some phase
  | phase@(.live _ _), .relocate _ => some phase
  | .live _ _, .publish => some .published
  | .live _ _, .abandon => some .abandoned
  | _, _ => none

def runDestinationObservations : DestinationTracePhase → List DestinationObservation →
    Option DestinationTracePhase
  | phase, [] => some phase
  | phase, observation :: rest =>
      (destinationTraceStep phase observation).bind fun next => runDestinationObservations next rest

def runDestinationTrace (id : DestinationId) (phase : DestinationTracePhase)
    (events : List ConstructionEvent) : Option DestinationTracePhase :=
  runDestinationObservations phase (destinationObservations id events)

def DestinationTracePhase.matchesProgress : DestinationTracePhase → DestinationProgress → Prop
  | .live _ _, .open _ | .live _ _, .suspended _ _ | .live _ _, .built _
  | .live _ _, .exiting _ _ | .live _ _, .attached _ | .live _ _, .retired => True
  | .published, .published _ | .published, .attached _ => True
  | .abandoned, .abandoned | .abandoned, .cancelled => True
  | _, _ => False

def DestinationTracePhase.matchesDestination (phase : DestinationTracePhase)
    (destination : PendingDestination) : Prop :=
  phase.matchesProgress destination.progress ∧
    match phase, destination.progress, destination.backing with
    | .live staged wrote, .open 0, .direct _ => staged = false ∧ wrote = false
    | .live staged wrote, .open 0, .staged _ _ => staged = true ∧ wrote = false
    | _, _, _ => True

def DestinationTraceProtocol (state : ConstructionState) : Prop :=
  ∀ id, match state.destinations[id]? with
    | none => runDestinationTrace id .unseen state.events = some .unseen
    | some destination => ∃ phase,
        runDestinationTrace id .unseen state.events = some phase ∧
        phase.matchesDestination destination

theorem destinationObservations_append (id : DestinationId)
    (before after : List ConstructionEvent) :
    destinationObservations id (before ++ after) =
      destinationObservations id before ++ destinationObservations id after := by
  exact List.filterMap_append

theorem runDestinationObservations_append (phase : DestinationTracePhase)
    (before after : List DestinationObservation) :
    runDestinationObservations phase (before ++ after) =
      (runDestinationObservations phase before).bind fun middle =>
        runDestinationObservations middle after := by
  induction before generalizing phase with
  | nil => rfl
  | cons observation rest ih =>
      simp only [List.cons_append, runDestinationObservations]
      cases destinationTraceStep phase observation <;> simp_all

theorem runDestinationTrace_append (id : DestinationId) (phase : DestinationTracePhase)
    (before after : List ConstructionEvent) :
    runDestinationTrace id phase (before ++ after) =
      (runDestinationTrace id phase before).bind fun middle =>
        runDestinationTrace id middle after := by
  simp only [runDestinationTrace, destinationObservations_append,
    runDestinationObservations_append]

theorem runDestinationTrace_prefix {id : DestinationId} {phase final : DestinationTracePhase}
    {before after : List ConstructionEvent}
    (accepted : runDestinationTrace id phase (before ++ after) = some final) :
    ∃ middle, runDestinationTrace id phase before = some middle ∧
      runDestinationTrace id middle after = some final := by
  rw [runDestinationTrace_append] at accepted
  cases first : runDestinationTrace id phase before with
  | none => simp [first] at accepted
  | some middle => exact ⟨middle, rfl, by simpa [first] using accepted⟩

theorem destinationTraceStep_terminal (observation : DestinationObservation) :
    destinationTraceStep .published observation = none ∧
    destinationTraceStep .abandoned observation = none := by
  cases observation <;> exact ⟨rfl, rfl⟩

theorem runDestinationObservations_terminal (observations : List DestinationObservation) :
    runDestinationObservations .published observations =
        (if observations.isEmpty then some .published else none) ∧
    runDestinationObservations .abandoned observations =
        (if observations.isEmpty then some .abandoned else none) := by
  cases observations with
  | nil => exact ⟨rfl, rfl⟩
  | cons observation rest =>
      simp only [runDestinationObservations,
        (destinationTraceStep_terminal observation).1,
        (destinationTraceStep_terminal observation).2]
      exact ⟨rfl, rfl⟩

theorem runDestinationTrace_no_events_after_publish {id : DestinationId}
    {before after : List ConstructionEvent} {final : DestinationTracePhase}
    (published : runDestinationTrace id .unseen before = some .published)
    (accepted : runDestinationTrace id .unseen (before ++ after) = some final) :
    destinationObservations id after = [] := by
  rw [runDestinationTrace_append, published] at accepted
  change runDestinationObservations .published (destinationObservations id after) = some final at accepted
  rw [(runDestinationObservations_terminal _).1] at accepted
  cases observations : destinationObservations id after with
  | nil => rfl
  | cons observation rest => simp [observations] at accepted

theorem runDestinationTrace_no_events_after_abandon {id : DestinationId}
    {before after : List ConstructionEvent} {final : DestinationTracePhase}
    (abandoned : runDestinationTrace id .unseen before = some .abandoned)
    (accepted : runDestinationTrace id .unseen (before ++ after) = some final) :
    destinationObservations id after = [] := by
  rw [runDestinationTrace_append, abandoned] at accepted
  change runDestinationObservations .abandoned (destinationObservations id after) = some final at accepted
  rw [(runDestinationObservations_terminal _).2] at accepted
  cases observations : destinationObservations id after with
  | nil => rfl
  | cons observation rest => simp [observations] at accepted

theorem destinationTraceStep_stage (phase next : DestinationTracePhase) :
    destinationTraceStep phase .stage = some next ↔
      phase = .live false false ∧ next = .live true false := by
  cases phase with
  | unseen | published | abandoned => simp [destinationTraceStep]
  | live staged wrote => cases staged <;> cases wrote <;> simp [destinationTraceStep, eq_comm]

theorem destinationTraceStep_begin (phase next : DestinationTracePhase) :
    destinationTraceStep phase .begin = some next ↔
      phase = .unseen ∧ next = .live false false := by
  cases phase <;> simp [destinationTraceStep, eq_comm]

theorem destinationTraceStep_ne_unseen {phase next : DestinationTracePhase}
    {observation : DestinationObservation}
    (accepted : destinationTraceStep phase observation = some next) : next ≠ .unseen := by
  intro unseen
  subst next
  cases phase <;> cases observation <;> simp_all [destinationTraceStep]
  split at accepted <;> simp_all

theorem runDestinationObservations_no_begin {phase final : DestinationTracePhase}
    {observations : List DestinationObservation} (seen : phase ≠ .unseen)
    (accepted : runDestinationObservations phase observations = some final) :
    DestinationObservation.begin ∉ observations := by
  induction observations generalizing phase with
  | nil => simp
  | cons observation rest ih =>
      simp only [runDestinationObservations] at accepted
      cases step : destinationTraceStep phase observation with
      | none => simp [step] at accepted
      | some next =>
          have notBegin : observation ≠ .begin := by
            intro equal
            subst observation
            exact seen ((destinationTraceStep_begin phase next).mp step).1
          have tail := ih (destinationTraceStep_ne_unseen step) (by simpa [step] using accepted)
          simpa only [List.mem_cons, not_or] using And.intro (Ne.symm notBegin) tail

theorem runDestinationObservations_initial_shape {final : DestinationTracePhase}
    {observations : List DestinationObservation}
    (accepted : runDestinationObservations .unseen observations = some final) :
    observations = [] ∨ ∃ rest, observations = .begin :: rest ∧ .begin ∉ rest := by
  cases observations with
  | nil => exact Or.inl rfl
  | cons observation rest =>
      right
      cases observation <;> simp only [runDestinationObservations, destinationTraceStep] at accepted
      all_goals try contradiction
      exact ⟨rest, rfl, runDestinationObservations_no_begin (by decide) accepted⟩

theorem runDestinationTrace_begin_once {id : DestinationId} {final : DestinationTracePhase}
    {events : List ConstructionEvent}
    (accepted : runDestinationTrace id .unseen events = some final) :
    (destinationObservations id events).count .begin ≤ 1 := by
  rcases runDestinationObservations_initial_shape accepted with empty | ⟨rest, equal, absent⟩
  · simp [empty]
  · simp [equal, List.count_eq_zero.mpr absent]

def DestinationTracePhase.stageBudget : DestinationTracePhase → Nat
  | .unseen | .live false false => 1
  | _ => 0

theorem destinationTraceStep_stage_budget {phase next : DestinationTracePhase}
    {observation : DestinationObservation}
    (accepted : destinationTraceStep phase observation = some next) :
    (if observation = .stage then 1 else 0) + next.stageBudget ≤ phase.stageBudget := by
  cases phase with
  | live staged wrote =>
      cases staged <;> cases wrote <;> cases observation <;> cases next <;>
        simp_all [destinationTraceStep, DestinationTracePhase.stageBudget]
  | unseen | published | abandoned =>
      cases observation <;> cases next <;>
        simp_all [destinationTraceStep, DestinationTracePhase.stageBudget]

theorem runDestinationObservations_stage_budget {phase final : DestinationTracePhase}
    {observations : List DestinationObservation}
    (accepted : runDestinationObservations phase observations = some final) :
    observations.count .stage + final.stageBudget ≤ phase.stageBudget := by
  induction observations generalizing phase with
  | nil =>
      simp only [runDestinationObservations, Option.some.injEq] at accepted
      subst final
      simp
  | cons observation rest ih =>
      simp only [runDestinationObservations] at accepted
      cases step : destinationTraceStep phase observation with
      | none => simp [step] at accepted
      | some next =>
          have tail := ih (by simpa [step] using accepted)
          have head := destinationTraceStep_stage_budget step
          by_cases stage : observation = .stage
          · subst observation
            simp only [List.count_cons_self, ↓reduceIte] at *
            omega
          · simp [List.count_cons, stage, Ne.symm stage] at *
            omega

theorem runDestinationTrace_stage_once {id : DestinationId} {final : DestinationTracePhase}
    {events : List ConstructionEvent}
    (accepted : runDestinationTrace id .unseen events = some final) :
    (destinationObservations id events).count .stage ≤ 1 := by
  have budget := runDestinationObservations_stage_budget accepted
  simp only [DestinationTracePhase.stageBudget] at budget
  omega

theorem initial_destination_trace_protocol : DestinationTraceProtocol ConstructionState.initial := by
  intro id
  simp [ConstructionState.initial, runDestinationTrace, destinationObservations,
    runDestinationObservations]

def PreservesDestinationTraceProtocol (action : ConstructionM α) : Prop :=
  ∀ state, DestinationTraceProtocol state → DestinationTraceProtocol (action state).finalState

theorem preservesDestinationTraceProtocol_pure (value : α) :
    PreservesDestinationTraceProtocol (pure value) := fun _ valid => valid

theorem preservesDestinationTraceProtocol_fail (kind : ConstructionFault) :
    PreservesDestinationTraceProtocol (ConstructionM.fail (α := α) kind) := fun _ valid => valid

theorem preservesDestinationTraceProtocol_get :
    PreservesDestinationTraceProtocol ConstructionM.get := fun _ valid => valid

theorem preservesDestinationTraceProtocol_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : PreservesDestinationTraceProtocol action)
    (remaining : ∀ value, PreservesDestinationTraceProtocol (next value)) :
    PreservesDestinationTraceProtocol (action >>= next) := by
  intro state valid
  have middle := first state valid
  cases result : action state with
  | ok value after =>
      simp only [result, ConstructionResult.finalState] at middle
      simpa only [bind, result] using remaining value after middle
  | fault kind after => simpa only [bind, result, ConstructionResult.finalState] using middle

theorem reserveStorage_destination_trace_protocol (bytes : ByteArray) (count : Nat) :
    PreservesDestinationTraceProtocol (reserveStorage bytes count) := by
  intro state valid
  exact valid

theorem appendStdout_destination_trace_protocol (bytes : ByteArray) :
    PreservesDestinationTraceProtocol (appendStdout bytes) := by
  intro state valid
  exact valid

def DestinationStorageReferencesValid (state : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (destination : PendingDestination),
    state.destinations[id]? = some destination →
      destination.storage < state.storage.size ∧
        destination.backing.receiverStorage < state.storage.size

def DestinationLifecycleInvariant (state : ConstructionState) : Prop :=
  DestinationTraceProtocol state ∧ DestinationCapabilitiesIndexed state ∧
    DestinationStorageReferencesValid state

theorem initial_destination_lifecycle_invariant :
    DestinationLifecycleInvariant ConstructionState.initial := by
  refine ⟨initial_destination_trace_protocol, initial_destination_capabilities, ?_⟩
  intro id destination present
  simp [ConstructionState.initial] at present

theorem destinationLifecycleInvariant_storage_frame (state : ConstructionState)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with storage := storage } := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro id destination present
  simpa only [size] using valid.2.2 id destination present

theorem reserveStorage_destination_lifecycle_invariant (bytes : ByteArray) (count : Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (reserveStorage bytes count state).finalState := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro id destination present
  have references := valid.2.2 id destination present
  change destination.storage < (state.storage.push ⟨bytes, count⟩).size ∧
    destination.backing.receiverStorage < (state.storage.push ⟨bytes, count⟩).size
  simp only [Array.size_push]
  exact ⟨Nat.lt.step references.1, Nat.lt.step references.2⟩

theorem appendStdout_destination_lifecycle_invariant (bytes : ByteArray)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (appendStdout bytes state).finalState := valid

end Goose.Construct
