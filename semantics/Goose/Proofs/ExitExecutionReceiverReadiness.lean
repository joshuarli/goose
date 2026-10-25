import Goose.Proofs.ExitExecutionLiveCarrierLanding
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

local syntax "receiver_split_at " ident : tactic
elab_rules : tactic
  | `(tactic| receiver_split_at $name:ident) => do
      let hypothesis ← Lean.Elab.Tactic.getFVarId name
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.SplitIf.splitIfAt? goal (← Lean.Meta.inferType (.fvar hypothesis)) none
          | Lean.throwError "no receiver condition"
        return [yes.mvarId, no.mvarId]

private theorem openDestination_receiver_row (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (id : Nat) (executed : openDestination target capability layout knownCount state = .ok id after) :
    id = state.destinations.size ∧ after.destinationSuccessors = state.destinationSuccessors ∧
      after.destinations.size = state.destinations.size + 1 ∧
      ∃ destination, after.destinations[id]? = some destination ∧ destination.use = .receiver := by
  rw [openDestination_transition] at executed
  simp only [lookupStorage_result, bind] at executed
  cases targetFound : state.storage[target]? with
  | none => simp only [targetFound] at executed; cases executed
  | some receiver =>
    have targetInside := (Array.getElem?_eq_some_iff.mp targetFound).1
    cases knownCount <;> cases layout <;> cases request : capability.request <;>
      repeat' first
        | contradiction
        | simp_all only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            replaceStorage_result, reserveStorage, emit_result,
            hasPrefix_result, bind, pure, ConstructionResult.ok.injEq,
            Array.size_push, PendingDestination.storage, DestinationBacking.writeStorage,
            DestinationBacking.receiverStorage, Array.getElem?_push,
            Nat.lt_irrefl, ↓reduceIte, reduceCtorEq,
            beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.and_false,
            Bool.false_eq_true]
        | receiver_split_at executed
        | split at executed
        | rcases executed with ⟨rfl, rfl⟩
    all_goals exact ⟨True.intro, True.intro, True.intro, _, rfl, rfl⟩

private def receiver_self_ready (state : ExecutionState) (id : Nat) (destination : PendingDestination)
    (present : state.construction.destinations[id]? = some destination)
    (receiver : destination.use = .receiver)
    (terminal : state.construction.destinationSuccessors.lookup id = none) :
    ReceivingCarrierLandingReady state id id := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  refine ⟨id, destination, destination, ?_, present, present, .refl _, .receiver receiver, Nat.le_refl _⟩
  simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]

theorem openDestination_receiving_ready (state after : ConstructionState) (target : Nat)
    (capability : Goose.Core.Destination Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (id : Nat) (valid : DestinationSuccessorsValid state)
    (executed : openDestination target capability layout knownCount state = .ok id after)
    (execution : ExecutionState) (construction : execution.construction = after) :
    Nonempty (ReceivingCarrierLandingReady execution id id) := by
  obtain ⟨newId, successors, size, destination, present, receiver⟩ :=
    openDestination_receiver_row state after target capability layout knownCount id executed
  apply Nonempty.intro
  apply receiver_self_ready execution id destination (by simpa only [construction] using present) receiver
  rw [construction, successors]
  cases edge : state.destinationSuccessors.lookup id with
  | none => rfl
  | some next =>
    obtain ⟨lower, upper⟩ := valid id next edge
    rw [newId] at lower
    exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt lower) upper)

private theorem receivingLayout_open_ready (layout : LayoutEnv) (ty : Ty)
    (state after : ExecutionState) (target id : Nat) (origin : Goose.Core.OriginId)
    (capability : Goose.Core.Destination Ty) (knownCount : Option Nat)
    (valid : DestinationSuccessorsValid state.construction)
    (executed : ((receivingLayout layout ty >>= fun selected =>
      liftConstruction origin (openDestination target capability selected knownCount)) state) = .ok id after) :
    Nonempty (ReceivingCarrierLandingReady after id id) := by
  have query := stateQuery_receivingLayout layout ty state
  cases evaluated : receivingLayout layout ty state with
  | ok selected middle =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at query
    subst middle
    simp only [bind, evaluated, liftConstruction] at executed
    cases opened : openDestination target capability selected knownCount state.construction with
    | fault reason final => simp only [opened] at executed; cases executed
    | ok value final =>
      simp only [opened] at executed
      cases executed
      exact openDestination_receiving_ready state.construction final target capability selected knownCount id valid opened _ rfl
  | stop reason middle | escape target carriers middle | jump target kind middle =>
    simp only [bind, evaluated] at executed
    cases executed

theorem newDestination_receiving_ready (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Nat) (knownCount : Option Nat) (state after : ExecutionState) (id : Nat)
    (valid : DestinationSuccessorsValid state.construction)
    (executed : newDestination layout owner ty request origin storage knownCount state = .ok id after) :
    Nonempty (ReceivingCarrierLandingReady after id id) := by
  cases storage with
  | some target =>
    simp only [newDestination, bind, pure] at executed
    exact receivingLayout_open_ready layout ty state after target id origin _ knownCount valid executed
  | none =>
    let prepared : ExecutionState := { state with construction :=
      { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
    simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set,
      bind, pure] at executed
    exact receivingLayout_open_ready layout ty prepared after state.construction.storage.size id origin _ knownCount valid executed

#print axioms openDestination_receiving_ready
#print axioms newDestination_receiving_ready

end Goose.Proofs.ExitExecution
