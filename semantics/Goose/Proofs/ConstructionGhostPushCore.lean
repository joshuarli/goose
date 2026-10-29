import Goose.Proofs.ConstructionGhostGlobalStep

namespace Goose.Proofs.ConstructionGhostPushCore
open Goose.Construct

def ownerExtensionSnapshot (stored : StoredValue) : EvalM (Option PendingDestination) := do
  match stored.destination with
  | none => pure none
  | some id => do
      let parent ← getDestination id
      pure (match parent.progress with | .built _ => some parent | _ => none)

def ownerExtensionAction (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) : EvalM α := fun state =>
  let finish := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
    match snapshot with
    | none => result state'
    | some parent =>
        match restoreCompletedOwner parent destination
            (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) state' with
        | .ok () final => result final
        | .stop reason final => ExecutionStep.stop reason final
        | .escape target carriers final => ExecutionStep.escape target carriers final
        | .jump target kind final => ExecutionStep.jump target kind final
  match action destination state with
  | .escape target carriers state' => finish carriers (.escape target carriers) state'
  | .jump target kind state' =>
      finish (match kind with | .breakValue carriers => carriers | .continueLoop => []) (.jump target kind) state'
  | result => result

theorem ownerExtension_source (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (before : ExecutionState) :
    withOwnerExtension stored allocate action before =
      (do let snapshot ← ownerExtensionSnapshot stored
          let destination ← allocate
          ownerExtensionAction snapshot destination action) before := by
  cases destinationEq : stored.destination with
  | none => simp [withOwnerExtension, ownerExtensionSnapshot, ownerExtensionAction, destinationEq, bind, pure] <;> rfl
  | some id =>
      simp only [withOwnerExtension, ownerExtensionSnapshot, ownerExtensionAction, destinationEq, bind, pure]
      cases getDestination id before <;> rfl

theorem pushValue_fixed_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) (operand : Expr) (origin : Goose.Core.OriginId) (before placed readState sampled : ExecutionState)
    (location : Goose.Core.Loc) (stored : StoredValue) (bytes : ByteArray) (run : SampledRun)
    (placedEq : evalPlace fuel config environment owner before = .ok location placed)
    (readEq : readLoc fuel config.layout location placed = .ok (.stored stored) readState)
    (sampleEq : sampledStored stored readState = .ok (bytes, run) sampled) (fixed : run.element.nonfixed = false) :
    pushValue (fuel + 1) config environment owner operand origin before =
      (do let value ← evalValue fuel config environment operand
          let (count, _) ← arrayLength (← readLoc fuel config.layout location)
          appendFixedValues fuel config.layout location [value] origin
          pure (Value.ref ⟨location.root, location.path ++ [count]⟩)) sampled := by
  simp only [pushValue, bind, placedEq, readEq, sampleEq, fixed, Bool.false_eq_true, ↓reduceIte, pure]

theorem pushValue_nonfixed_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) (operand : Expr) (origin : Goose.Core.OriginId) (before placed readState sampled snapshotState buildState : ExecutionState)
    (location : Goose.Core.Loc) (stored : StoredValue) (bytes : ByteArray) (run : SampledRun)
    (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId)
    (placedEq : evalPlace fuel config environment owner before = .ok location placed)
    (readEq : readLoc fuel config.layout location placed = .ok (.stored stored) readState)
    (sampleEq : sampledStored stored readState = .ok (bytes, run) sampled) (nonfixed : run.element.nonfixed = true)
    (snapshotEq : ownerExtensionSnapshot stored sampled = .ok snapshot snapshotState)
    (allocated : openElementReceiving config.layout environment.act location stored run.element
      (producerCount? ⟨config.module, environment.vars⟩ operand) origin snapshotState = .ok destination buildState) :
    pushValue (fuel + 1) config environment owner operand origin before =
      (do ownerExtensionAction snapshot destination (fun destination => do
            buildExpr fuel config environment destination operand
            publishElementReceiving fuel config.layout location stored (← completedReceivingDestination destination) origin)
          pure (Value.ref ⟨location.root, location.path ++ [run.count]⟩)) buildState := by
  simp only [pushValue, bind, placedEq, readEq, sampleEq, nonfixed, ↓reduceIte]
  rw [ownerExtension_source]
  simp only [bind, snapshotEq, allocated, pure]

#print axioms pushValue_fixed_source
#print axioms pushValue_nonfixed_source

#print axioms ownerExtension_source
end Goose.Proofs.ConstructionGhostPushCore
