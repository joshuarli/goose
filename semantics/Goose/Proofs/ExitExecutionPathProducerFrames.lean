import Goose.Proofs.ExitExecutionPathProducers
import Goose.Proofs.ExitExecutionCleanupFrames

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def producerCleanupObservation (state : ExecutionState) :=
  (state.construction.stdout, state.objects)

private abbrev KeepsProducerCleanup (action : EvalM α) : Prop :=
  ∀ state, producerCleanupObservation (Goose.Proofs.Exit.stepState (action state)) = producerCleanupObservation state

private theorem producerCleanup_query (action : EvalM α) (query : StateQuery action) :
    KeepsProducerCleanup action := by
  intro state
  rw [query state]

private theorem producerCleanup_bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsProducerCleanup action) (remaining : ∀ value, KeepsProducerCleanup (next value)) :
    KeepsProducerCleanup (action >>= next) :=
  Goose.Proofs.Exit.runtime_bind_frames producerCleanupObservation action next first remaining

private theorem producerCleanup_lift (origin : Goose.Core.OriginId) (action : ConstructionM α)
    (stdout : ∀ state, (action state).finalState.stdout = state.stdout) :
    KeepsProducerCleanup (liftConstruction origin action) := by
  intro state
  exact Prod.ext (Goose.Proofs.Exit.runtime_lift_frames_output origin action stdout state)
    (Goose.Proofs.Exit.runtime_lift_frames_objects origin action state)

private theorem cleanupDestination_producerFrame (origin : Goose.Core.OriginId) (id : Nat)
    (carriers : List Carrier) : KeepsProducerCleanup (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply producerCleanup_bind
  · exact producerCleanup_query _ (stateQuery_getDestination _)
  · intro destination
    split
    · exact producerCleanup_query _ (stateQuery_pure _)
    · apply producerCleanup_bind
      · exact producerCleanup_query _ stateQuery_get
      · intro state
        split
        · exact producerCleanup_lift _ _ (fun state => abandonPreservingExit_stdout state _ _)
        · split
          · exact producerCleanup_query _ (stateQuery_pure _)
          · exact producerCleanup_lift _ _ (abandonTree_stdout _)

theorem cleanupReceivingDestination_frame (origin : Goose.Core.OriginId) (incoming : Nat)
    (carriers : List Carrier) (initial : ExecutionState) :
    let final := Goose.Proofs.Exit.stepState (cleanupReceivingDestination origin incoming carriers initial)
    final.construction.stdout = initial.construction.stdout ∧ final.objects = initial.objects := by
  have frame : KeepsProducerCleanup (cleanupReceivingDestination origin incoming carriers) := by
    unfold cleanupReceivingDestination
    apply producerCleanup_bind
    · exact producerCleanup_query _ (stateQuery_receivingDestination _)
    · intro id
      exact cleanupDestination_producerFrame origin id carriers
  exact ⟨congrArg Prod.fst (frame initial), congrArg Prod.snd (frame initial)⟩

theorem ProducerEscapeResult.frame {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared before final : ExecutionState}
    {carriers : List Carrier}
    (result : ProducerEscapeResult config parent initial child prepared carriers before final) :
    final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  cases result with
  | @produce fuel environment incoming planned channels expression initial prepared ready before final β child receiving body carriers landed =>
      subst final
      cases expression <;> exact ⟨rfl, rfl⟩
  | @build fuel environment incoming destination expression initial prepared ready before final β child renewed body carriers cleaned =>
      have frame := cleanupReceivingDestination_frame (expressionOrigin expression) destination carriers
        (producerBodyEscapedState expression prepared before)
      rw [cleaned] at frame
      cases expression <;> exact frame
  | elementBuild => exact ⟨rfl, rfl⟩
  | elementValue => exact ⟨rfl, rfl⟩

#print axioms cleanupReceivingDestination_frame

#print axioms ProducerEscapeResult.frame

theorem reached_produce_escape_frame {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (channels : List Channel) (expression : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.produce fuel environment channels expression) initial)
    (escaped : evalProduce fuel config environment channels expression initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ProducerEscapeResult config (.produce fuel environment channels expression) initial child prepared carriers before final ∧
      child.action config prepared = .escape address carriers before ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨β, child, prepared, before, childReached, result, evaluated⟩ :=
    reached_produce_escape_inv channels expression reached escaped
  obtain ⟨stdout, objects⟩ := result.frame
  exact ⟨β, child, prepared, before, childReached, result, evaluated, stdout, objects⟩

#print axioms reached_produce_escape_frame

theorem reached_build_escape_frame {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (destination : Nat) (expression : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.build fuel environment destination expression) initial)
    (escaped : buildExpr fuel config environment destination expression initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ProducerEscapeResult config (.build fuel environment destination expression) initial child prepared carriers before final ∧
      child.action config prepared = .escape address carriers before ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨β, child, prepared, before, childReached, result, evaluated⟩ :=
    reached_build_escape_inv destination expression reached escaped
  obtain ⟨stdout, objects⟩ := result.frame
  exact ⟨β, child, prepared, before, childReached, result, evaluated, stdout, objects⟩

#print axioms reached_build_escape_frame

theorem reached_element_escape_frame {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (destination : Nat) (element : Ty) (operand : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.element fuel environment destination element operand) initial)
    (escaped : buildElement fuel config environment destination element operand initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ProducerEscapeResult config (.element fuel environment destination element operand) initial child prepared carriers before final ∧
      child.action config prepared = .escape address carriers before ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨β, child, prepared, before, childReached, result, evaluated⟩ :=
    reached_element_escape_inv destination element operand reached escaped
  obtain ⟨stdout, objects⟩ := result.frame
  exact ⟨β, child, prepared, before, childReached, result, evaluated, stdout, objects⟩

#print axioms reached_element_escape_frame

end Goose.Proofs.ExitExecution
