import Goose.Proofs.ExitExecutionInvocationStatementsCauses
import Goose.Proofs.ExitExecutionInvocationStatementsNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem bind_escape_inv (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    action initial = .escape address carriers final ∨
      ∃ value prepared, action initial = .ok value prepared ∧ next value prepared = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value prepared =>
      exact Or.inr ⟨value, prepared, rfl, by simpa only [bind, evaluated] using escaped⟩
  | escape target payload before =>
      simp only [bind, evaluated] at escaped
      cases escaped
      exact Or.inl rfl
  | stop reason before | jump target kind before =>
      simp only [bind, evaluated] at escaped
      cases escaped

private theorem native_bind_escape_inv (action : EvalM α) (next : α → EvalM β)
    (never : ProducerNeverEscapes action)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ value prepared, action initial = .ok value prepared ∧ next value prepared = .escape address carriers final := by
  rcases bind_escape_inv action next initial final address carriers escaped with failure | normal
  · exact False.elim (never initial address carriers final failure)
  · exact normal

private theorem ownerSnapshot_neverEscapes (stored : StoredValue) :
    ProducerNeverEscapes ((match stored.destination with
      | none => pure none
      | some id => do
          let parent ← getDestination id
          pure (match parent.progress with | .built _ => some parent | _ => none)) : EvalM (Option PendingDestination)) := by
  cases stored.destination with
  | none => exact producerNeverEscapes_pure _
  | some id =>
      apply producerNeverEscapes_bind
      · exact producerNeverEscapes_getDestination _
      · intro parent
        exact producerNeverEscapes_pure _

private theorem bind_assoc (action : EvalM α) (next : α → EvalM β) (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated]

private theorem bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

private def ownerGuard (snapshot : Option PendingDestination) (destination : Nat) (action : EvalM α) : EvalM α := fun state =>
  let finish := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
    match snapshot with
    | none => result state'
    | some parent =>
        match restoreCompletedOwner parent destination
            (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) state' with
        | .ok () final => result final
        | .stop reason final => .stop reason final
        | .escape target carriers final => .escape target carriers final
        | .jump target kind final => .jump target kind final
  match action state with
  | .escape target carriers state' => finish carriers (.escape target carriers) state'
  | .jump target kind state' =>
      finish (match kind with | .breakValue carriers => carriers | .continueLoop => []) (.jump target kind) state'
  | result => result

private theorem ownerExtension_action (stored : StoredValue) (allocate : EvalM Nat) (action : Nat → EvalM α) :
    withOwnerExtension stored allocate action = ((do
      let snapshot ← ((match stored.destination with
        | none => pure none
        | some id => do
            let parent ← getDestination id
            pure (match parent.progress with | .built _ => some parent | _ => none)) : EvalM (Option PendingDestination))
      let destination ← allocate
      ownerGuard snapshot destination (action destination)) : EvalM α) := by
  unfold withOwnerExtension ownerGuard
  cases stored.destination <;> simp only [bind_assoc, bind_pure]
  all_goals rfl

private theorem ownerExtension_escape_inv (stored : StoredValue) (allocate : EvalM Nat)
    (action : Nat → EvalM α) (never : ProducerNeverEscapes allocate)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : withOwnerExtension stored allocate action initial = .escape address carriers final) :
    ∃ snapshot sampled destination prepared before,
      StatementOwnerSnapshot stored initial snapshot sampled ∧
      allocate sampled = .ok destination prepared ∧
      action destination prepared = .escape address carriers before := by
  rw [ownerExtension_action] at escaped
  obtain ⟨snapshot, sampled, snapshotSelected, remaining⟩ :=
    native_bind_escape_inv _ _ (ownerSnapshot_neverEscapes stored) initial final address carriers escaped
  obtain ⟨destination, prepared, allocated, guarded⟩ :=
    native_bind_escape_inv _ _ never sampled final address carriers remaining
  refine ⟨snapshot, sampled, destination, prepared, ?_⟩
  have snapshotPrefix : StatementOwnerSnapshot stored initial snapshot sampled := .actual initial sampled snapshot snapshotSelected
  dsimp only [ownerGuard] at guarded
  cases evaluated : action destination prepared with
  | ok value after | stop reason after =>
      simp only [evaluated] at guarded
      cases guarded
  | escape target payload before =>
      simp only [evaluated] at guarded
      cases snapshot with
      | none =>
          simp only [] at guarded
          cases guarded
          exact ⟨_, snapshotPrefix, allocated, rfl⟩
      | some parent =>
          cases restored : restoreCompletedOwner parent destination
              (payload.filterMap fun (carrier : Carrier) => match carrier with | .completed id => some id | _ => none) before with
          | ok value after =>
              cases value
              simp only [restored] at guarded
              cases guarded
              exact ⟨_, snapshotPrefix, allocated, rfl⟩
          | stop reason after | jump target kind after =>
              simp only [restored] at guarded
              cases guarded
          | escape target payload after =>
              exact False.elim (statementNeverEscapes_restoreCompletedOwner _ _ _ _ _ _ _ restored)
  | jump target kind before =>
      simp only [evaluated] at guarded
      cases snapshot with
      | none => cases guarded
      | some parent =>
          cases restored : restoreCompletedOwner parent destination
              ((match kind with | .breakValue carriers => carriers | .continueLoop => ([] : List Carrier)).filterMap
                fun (carrier : Carrier) => match carrier with | .completed id => some id | _ => none) before with
          | ok value after | stop reason after | jump target kind after =>
              simp only [restored] at guarded
              cases guarded
          | escape target payload after =>
              exact False.elim (statementNeverEscapes_restoreCompletedOwner _ _ _ _ _ _ _ restored)

private theorem bind_left_escape_inv (action : EvalM α) (next : α → EvalM β)
    (never : ∀ value, ProducerNeverEscapes (next value))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    action initial = .escape address carriers final := by
  rcases bind_escape_inv action next initial final address carriers escaped with failure | normal
  · exact failure
  · obtain ⟨value, prepared, _, remaining⟩ := normal
    exact False.elim (never value prepared address carriers final remaining)

private theorem ownerExtension_neverEscapes (stored : StoredValue) (allocate : EvalM Nat)
    (action : Nat → EvalM α) (allocationNever : ProducerNeverEscapes allocate)
    (actionNever : ∀ destination, ProducerNeverEscapes (action destination)) :
    ProducerNeverEscapes (withOwnerExtension stored allocate action) := by
  intro initial address carriers final escaped
  obtain ⟨snapshot, sampled, destination, prepared, before, _, _, child⟩ :=
    ownerExtension_escape_inv stored allocate action allocationNever initial final address carriers escaped
  exact actionNever destination prepared address carriers before child

private theorem ownerFinish_neverEscapes (fuel : Nat) (config : EvalConfig) (location : Goose.Core.Loc)
    (stored : StoredValue) (destination : Nat) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes ((do
      publishOwner fuel config.layout location stored (← completedReceivingDestination destination) origin) : EvalM Unit) := by
  apply producerNeverEscapes_bind
  · exact producerNeverEscapes_completedReceivingDestination _
  · intro completed
    exact statementNeverEscapes_publishOwner _ _ _ _ _ _

theorem statementAssignWhole_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) (replacement : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.assignWhole owner replacement origin) initial = .escape address carriers final) :
    StatementCausalChild config (.statement (fuel + 1) environment (.assignWhole owner replacement origin)) initial address carriers := by
  rw [execStmt] at escaped
  rcases bind_escape_inv _ _ initial final address carriers escaped with placeFailed | normalPlace
  · exact ⟨Goose.Core.Loc, .place fuel environment owner, initial, final,
      .assignWholePlace fuel environment owner replacement origin initial, placeFailed⟩
  · obtain ⟨location, located, placeSelected, afterPlace⟩ := normalPlace
    obtain ⟨truncatedUnit, truncated, truncation, afterTruncation⟩ :=
      native_bind_escape_inv _ _ (valueNeverEscapes_truncateOwner _ _ _ _ _) located final address carriers afterPlace
    cases truncatedUnit
    obtain ⟨value, read, storedSelected, afterRead⟩ :=
      native_bind_escape_inv _ _ (producerNeverEscapes_readLoc _ _ _) truncated final address carriers afterTruncation
    cases value <;> try exact False.elim (producerNeverEscapes_fault .shape read address carriers final afterRead)
    case stored stored =>
      dsimp only [] at afterRead
      cases countSelected : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ replacement with
      | none =>
          simp only [materializeProducer, countSelected, bind_pure] at afterRead
          have wrapper := bind_left_escape_inv _ _ (fun _ => producerNeverEscapes_pure _)
            read final address carriers afterRead
          obtain ⟨snapshot, sampled, destination, prepared, before, snapshotSelected, allocation, actionEscaped⟩ :=
            ownerExtension_escape_inv stored _ _ (statementNeverEscapes_ownerDestination _ _ _ _ _)
              read final address carriers wrapper
          have child := bind_left_escape_inv _ _ (fun _ => ownerFinish_neverEscapes fuel config location stored destination origin)
            prepared before address carriers actionEscaped
          have setup : StatementOwnerBuildPrefix fuel config environment (.assignWhole owner replacement origin) initial snapshot destination prepared := by
            refine .whole owner replacement origin initial located truncated read read sampled prepared
              location stored snapshot destination placeSelected truncation storedSelected ?_ snapshotSelected ?_
            · simp only [materializeProducer, countSelected, pure]
            · exact allocation
          exact ⟨Unit, .build fuel environment destination replacement, prepared, before,
            .assignWholeBuild fuel environment owner replacement origin initial prepared destination snapshot setup, child⟩
      | some count =>
          simp only [materializeProducer, countSelected, bind_assoc] at afterRead
          rcases bind_escape_inv _ _ read final address carriers afterRead with valueFailed | normalValue
          · have setup : ((do
                let location ← evalPlace fuel config environment owner
                truncateOwner fuel config.layout location 0 origin
                let .stored stored ← readLoc fuel config.layout location | fault .shape
                pure stored) : EvalM StoredValue) initial = .ok stored read := by
              simp only [bind, placeSelected, truncation, storedSelected, pure]
            exact ⟨Value, .value fuel environment replacement, read, final,
              .assignWholeMaterialize fuel environment owner replacement origin initial read stored count setup countSelected, valueFailed⟩
          · obtain ⟨value, evaluated, valueSelected, remaining⟩ := normalValue
            cases value <;> try exact False.elim (producerNeverEscapes_fault .shape evaluated address carriers final remaining)
            case fixed values =>
              simp only [bind_pure] at remaining
              have wrapper := bind_left_escape_inv _ _ (fun _ => producerNeverEscapes_pure _)
                evaluated final address carriers remaining
              refine False.elim ((ownerExtension_neverEscapes stored _ _
                (statementNeverEscapes_ownerDestination _ _ _ _ _) ?_) evaluated address carriers final wrapper)
              intro destination
              apply producerNeverEscapes_bind
              · exact producerNeverEscapes_copyValue _ _ _ _ _ _
              · intro copied
                exact ownerFinish_neverEscapes fuel config location stored destination origin

end Goose.Proofs.ExitExecution
