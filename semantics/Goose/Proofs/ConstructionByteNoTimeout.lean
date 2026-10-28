import Goose.Proofs.ConstructionAcceptedByteTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def LocalConstructionAction (action : EvalM α) : Prop :=
  ∀ state, match action state with
    | .ok _ _ => True
    | .stop reason _ => reason ≠ .timeout
    | .escape _ _ _ | .jump _ _ _ => False

theorem LocalConstructionAction.pure (value : α) : LocalConstructionAction (pure value : EvalM α) := by
  intro state
  trivial

theorem LocalConstructionAction.bind {action : EvalM α} {next : α → EvalM β}
    (first : LocalConstructionAction action) (second : ∀ value, LocalConstructionAction (next value)) :
    LocalConstructionAction (action >>= next) := by
  intro state
  have current := first state
  cases evaluated : action state <;> simp only [Bind.bind, evaluated] at current ⊢
  case ok value after => exact second value after
  case stop reason after => exact current

theorem LocalConstructionAction.lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    LocalConstructionAction (liftConstruction origin action) := by
  intro state
  unfold liftConstruction
  cases result : action state.construction with
  | ok value after => trivial
  | fault kind after => cases kind <;> simp

theorem bytes_writeLoop_local (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat) :
    LocalConstructionAction ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) := by
  induction bytes with
  | nil => simpa only [List.forIn_nil] using LocalConstructionAction.pure PUnit.unit
  | cons byte rest ih =>
    simp only [List.forIn_cons]
    apply LocalConstructionAction.bind
    · apply LocalConstructionAction.bind (LocalConstructionAction.lift origin _)
      intro value
      exact LocalConstructionAction.pure _
    · intro step
      cases step with
      | done value => exact LocalConstructionAction.pure value
      | yield value => cases value; exact ih

theorem protectDestination_local (origin : Goose.Core.OriginId) (id : Nat) (action : EvalM α)
    (localAction : LocalConstructionAction action) : LocalConstructionAction (protectDestination origin id action) := by
  intro state
  have valid := localAction state
  unfold protectDestination
  cases evaluated : action state <;> simp only [evaluated] at valid ⊢
  all_goals assumption

theorem buildExpr_byteOwner_local (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (type : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    LocalConstructionAction (buildExpr (fuel + 1) config environment id (.bytes type bytes origin)) := by
  simp only [buildExpr]
  apply LocalConstructionAction.bind (LocalConstructionAction.lift origin _)
  intro destination
  apply protectDestination_local
  apply LocalConstructionAction.bind (bytes_writeLoop_local bytes origin destination)
  intro value
  cases value
  exact LocalConstructionAction.lift origin _

theorem LocalConstructionAction.fault (kind : Goose.Core.FaultKind) : LocalConstructionAction (fault kind : EvalM α) := by
  simp [LocalConstructionAction, Goose.Construct.fault, EvalM.stop]

theorem getDestination_local (id : Nat) : LocalConstructionAction (getDestination id) := by
  intro state
  simp only [getDestination, EvalM.get, bind, pure, Goose.Construct.fault]
  cases state.construction.destinations[id]? <;> simp [EvalM.stop]

theorem completedReceivingDestination_local (id : Nat) : LocalConstructionAction (completedReceivingDestination id) := by
  unfold completedReceivingDestination receivingDestination
  apply LocalConstructionAction.bind (LocalConstructionAction.lift 0 _)
  intro selected
  unfold completedDestination
  apply LocalConstructionAction.bind (getDestination_local selected)
  intro destination
  cases destination.progress <;> first | exact LocalConstructionAction.pure _ | exact LocalConstructionAction.fault _

theorem publishCompleted_local (origin : Goose.Core.OriginId) (id : Nat) :
    LocalConstructionAction (publishCarriers origin [.completed id]) := by
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id]
  exact LocalConstructionAction.lift origin _

theorem carrierCompleted_local (id : Nat) : LocalConstructionAction (carrierValue (.completed id)) := by
  simp only [carrierValue]
  apply LocalConstructionAction.bind
  · unfold storedDestination
    apply LocalConstructionAction.bind (getDestination_local id)
    intro destination
    split
    · split <;> exact LocalConstructionAction.pure _
    · exact LocalConstructionAction.fault _
  · intro value
    exact LocalConstructionAction.pure _

theorem newByteDestination_local (config : EvalConfig) (environment : RuntimeActivation)
    (origin : Goose.Core.OriginId) (count : Nat) :
    LocalConstructionAction (newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some count)) := by
  simp only [newDestination, receivingLayout]
  apply LocalConstructionAction.bind (LocalConstructionAction.lift origin reserveStorage)
  intro storage
  simpa only [pure, bind] using LocalConstructionAction.lift origin (openDestination storage
    ⟨0, ⟨.local environment.act 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .value, 0, environment.act⟩
    .packed (some count))

theorem evalValue_byteOwner_local (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    LocalConstructionAction (evalValue (fuel + 2) config environment (.bytes (.varr (.int .u8)) bytes origin)) := by
  simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, ↓reduceIte]
  apply LocalConstructionAction.bind
  · apply LocalConstructionAction.bind (newByteDestination_local config environment origin bytes.length)
    intro destination
    apply LocalConstructionAction.bind (buildExpr_byteOwner_local fuel config environment destination _ bytes origin)
    intro value
    cases value
    apply LocalConstructionAction.bind (completedReceivingDestination_local destination)
    intro completed
    apply LocalConstructionAction.bind (publishCompleted_local origin completed)
    intro value
    cases value
    exact LocalConstructionAction.pure _
  · intro carrier
    cases carrier with
    | register value => exact LocalConstructionAction.pure value
    | completed id => exact carrierCompleted_local id
    | pendingNamed id => exact LocalConstructionAction.fault _

theorem evalValue_byteOwner_timeout_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before after : ExecutionState)
    (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (executed : evalValue fuel config frame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .stop .timeout after) :
    (after = before ∧ AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types) ∨
    ∃ id, AcceptedWorld config frame.initialized after ambient types live
      (freshReceivingRegion before id :: regions) pending ∧ AcceptedFrame config accepted frame after types := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, ExecutionStep.stop.injEq, true_and] at executed
    subst after
    exact Or.inl ⟨rfl, world, source⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      exact Or.inr (evalValue_byteOwner_timeout_world config accepted frame before after bytes origin
        ambient types live regions pending world source executed)
    | succ fuel =>
      have noTimeout := evalValue_byteOwner_local fuel config frame.interpretation.environment bytes origin before
      rw [executed] at noTimeout
      exact (noTimeout rfl).elim

#print axioms buildExpr_byteOwner_local
#print axioms evalValue_byteOwner_local
#print axioms evalValue_byteOwner_timeout_complete

end Goose.Proofs.ConstructionAcceptedExecution
