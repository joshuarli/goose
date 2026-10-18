import Goose.Proofs.ExitExecutionUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private abbrev NeverEscapes (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState),
    action state ≠ .escape address carriers final

private theorem neverEscapes_pure (value : α) : NeverEscapes (pure value) := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_get : NeverEscapes EvalM.get := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_fault (kind : Goose.Core.FaultKind) : NeverEscapes (fault (α := α) kind) := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    NeverEscapes (liftConstruction origin action) := by
  intro state address carriers final impossible
  cases result : action state.construction <;>
    simp only [liftConstruction, result] at impossible <;> cases impossible

private theorem neverEscapes_bind (action : EvalM α) (next : α → EvalM β)
    (first : NeverEscapes action) (remaining : ∀ value, NeverEscapes (next value)) :
    NeverEscapes (action >>= next) := by
  intro state address carriers final impossible
  cases result : action state with
  | ok value middle =>
      simp only [bind, result] at impossible
      exact remaining value middle address carriers final impossible
  | stop reason after | jump target kind after =>
      simp only [bind, result] at impossible
      cases impossible
  | escape target values after => exact first state target values after result

private theorem neverEscapes_mapM (action : α → EvalM β) (items : List α)
    (each : ∀ item, NeverEscapes (action item)) : NeverEscapes (items.mapM action) := by
  induction items with
  | nil => simpa only [List.mapM_nil] using neverEscapes_pure ([] : List β)
  | cons item rest previous =>
      rw [List.mapM_cons]
      apply neverEscapes_bind
      · exact each item
      · intro value
        apply neverEscapes_bind
        · exact previous
        · intro values; exact neverEscapes_pure _

private theorem neverEscapes_forIn (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (each : ∀ item current, NeverEscapes (action item current)) :
    NeverEscapes (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact neverEscapes_pure _
  | cons item rest previous =>
      rw [List.forIn_cons]
      apply neverEscapes_bind
      · exact each item initial
      · intro step
        cases step with
        | done value => exact neverEscapes_pure _
        | yield value => exact previous value

private theorem neverEscapes_rootOf (environment : RuntimeActivation) (localVar : Goose.Core.VarId) :
    NeverEscapes (rootOf environment localVar) := by
  intro state address carriers final impossible
  cases found : environment.vars[localVar]? with
  | none =>
      simp only [rootOf, found, fault, EvalM.stop] at impossible
      cases impossible
  | some descriptor =>
      cases scopeFound : environment.scopes.find? (fun entry => entry.1 == descriptor.scope) <;>
        simp only [rootOf, found, scopeFound, fault, EvalM.stop, pure] at impossible <;> cases impossible

elab "channels_escape_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected channel callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro value))

local syntax "channels_never_escape" : tactic
macro_rules
  | `(tactic| channels_never_escape) => `(tactic|
    repeat' first
      | with_reducible exact neverEscapes_pure _
      | with_reducible exact neverEscapes_get
      | with_reducible exact neverEscapes_fault _
      | with_reducible exact neverEscapes_lift _ _
      | with_reducible exact neverEscapes_rootOf _ _
      | with_reducible apply neverEscapes_bind
      | with_reducible apply neverEscapes_mapM
      | with_reducible apply neverEscapes_forIn
      | split
      | channels_escape_intro)

private theorem neverEscapes_exitSource (source : RuntimeActivation) (incoming : Nat) (operand : Expr) :
    NeverEscapes (exitSource source incoming operand) := by
  unfold exitSource receivingDestination
  channels_never_escape

private theorem neverEscapes_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : NeverEscapes (exitChannels source activation operands origin) := by
  unfold exitChannels receivingDestination
  repeat' first
    | with_reducible exact neverEscapes_exitSource _ _ _
    | channels_never_escape

private theorem neverEscapes_materializeOwnedCarriers (origin : Goose.Core.OriginId)
    (tokens : List Nat) (carriers : List Carrier) : NeverEscapes (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  channels_never_escape

private theorem neverEscapes_exitChannelCleanupBorrowed (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat) (cancel : Bool)
    (carriers : List Carrier) : NeverEscapes (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers) := by
  unfold exitChannelCleanupBorrowed borrowedExitChannelStep
  dsimp only
  channels_never_escape

private theorem finishBorrowedExitChannels_escape_result (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat) (cancel : Bool)
    (values : List Carrier) (result : ExecutionState → ExecutionStep (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : finishBorrowedExitChannels origin borrowed tokens cancel values result initial = .escape address carriers final) :
    ∃ after, exitChannelCleanupBorrowed origin borrowed tokens cancel values initial = .ok () after ∧
      result after = .escape address carriers final := by
  unfold finishBorrowedExitChannels at escaped
  cases cleanup : exitChannelCleanupBorrowed origin borrowed tokens cancel values initial with
  | ok ignored after =>
      cases ignored
      simp only [cleanup] at escaped
      exact ⟨after, rfl, escaped⟩
  | stop reason after | jump target kind after =>
      simp only [cleanup] at escaped
      cases escaped
  | escape target payload after =>
      exact False.elim (neverEscapes_exitChannelCleanupBorrowed origin borrowed tokens cancel values
        initial target payload after cleanup)

theorem withExitChannels_escape_origin (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : withExitChannels source activation operands origin action initial = .escape address carriers final) :
    ∃ channels prepared afterOperands,
      exitChannels source activation operands origin initial = .ok channels prepared ∧
      action channels prepared = .escape address carriers afterOperands ∧
      exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
        afterOperands = .ok () final := by
  rw [withExitChannels_decomposition] at escaped
  cases setup : exitChannels source activation operands origin initial with
  | stop reason after | jump target kind after =>
      simp only [setup] at escaped
      cases escaped
  | escape target payload after =>
      exact False.elim (neverEscapes_exitChannels source activation operands origin initial target payload after setup)
  | ok channels prepared =>
      simp only [setup] at escaped
      cases evaluated : action channels prepared with
      | stop reason after | jump target kind after =>
          simp only [evaluated] at escaped
          obtain ⟨afterCleanup, cleanup, impossible⟩ := finishBorrowedExitChannels_escape_result _ _ _ _ _ _ _ _ _ _ escaped
          cases impossible
      | escape target payload afterOperands =>
          simp only [evaluated] at escaped
          obtain ⟨afterCleanup, cleanup, emitted⟩ := finishBorrowedExitChannels_escape_result _ _ _ _ _ _ _ _ _ _ escaped
          cases emitted
          exact ⟨channels, prepared, afterOperands, rfl, evaluated, cleanup⟩
      | ok raw afterOperands =>
          simp only [evaluated] at escaped
          cases materialized : materializeOwnedCarriers origin
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands with
          | ok completed after | stop reason after | jump target kind after =>
              simp only [materialized] at escaped
              obtain ⟨afterCleanup, cleanup, impossible⟩ := finishBorrowedExitChannels_escape_result _ _ _ _ _ _ _ _ _ _ escaped
              cases impossible
          | escape target payload after =>
              exact False.elim (neverEscapes_materializeOwnedCarriers origin _ raw afterOperands target payload after materialized)

private theorem neverEscapes_targetActivation (config : EvalConfig) (targetId : Nat) :
    NeverEscapes (targetActivation config targetId) := by
  unfold targetActivation
  channels_never_escape

theorem returnFromForward_escape_produce_origin (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (targetId : Nat) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.returnFromForward targetId producer origin) initial =
      .escape address carriers final) :
    ∃ activation target discarded outer,
      targetActivation config targetId initial = .ok activation initial ∧
      config.module.targets[targetId]? = some target ∧
      initial.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      ((∃ channels prepared afterOperands,
          exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared ∧
          evalProduce fuel config environment channels producer prepared = .escape address carriers afterOperands ∧
          exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
            afterOperands = .ok () final) ∨
       ∃ channels prepared raw afterOperands afterMaterialized,
          exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared ∧
          evalProduce fuel config environment channels producer prepared = .ok raw afterOperands ∧
          materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            raw afterOperands = .ok carriers afterMaterialized ∧
          exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
            afterMaterialized = .ok () final ∧
          address = ⟨activation.act, .nonlocal targetId⟩) := by
  simp only [execStmt] at escaped
  cases selected : targetActivation config targetId initial with
  | stop reason after | jump target kind after =>
      simp only [bind, selected] at escaped
      cases escaped
  | escape target payload after =>
      exact False.elim (neverEscapes_targetActivation config targetId initial target payload after selected)
  | ok activation after =>
      obtain ⟨unchanged, target, discarded, outer, declared, stack, included, excluded⟩ :=
        targetActivation_selects_nearest config targetId initial after activation selected
      subst after
      refine ⟨activation, target, discarded, outer, rfl, declared, stack, included, excluded, ?_⟩
      cases evaluated : withExitChannels environment activation (List.replicate activation.channels.length producer) origin
          (fun channels => evalProduce fuel config environment channels producer) initial with
      | stop reason after | jump target kind after =>
          simp only [bind, selected, evaluated] at escaped
          cases escaped
      | escape target payload after =>
          simp only [bind, selected, evaluated] at escaped
          cases escaped
          obtain ⟨channels, prepared, afterOperands, setup, produced, canceled⟩ :=
            withExitChannels_escape_origin environment activation (List.replicate activation.channels.length producer) origin
              (fun channels => evalProduce fuel config environment channels producer) initial final address carriers evaluated
          exact Or.inl ⟨channels, prepared, afterOperands, setup, produced, canceled⟩
      | ok payload after =>
          simp only [bind, selected, evaluated, Goose.Construct.escaped] at escaped
          cases escaped
          obtain ⟨channels, prepared, raw, afterOperands, afterMaterialized, setup, produced, materialized, released⟩ :=
            withExitChannels_ok_origin environment activation (List.replicate activation.channels.length producer) origin
              (fun channels => evalProduce fuel config environment channels producer) initial final carriers evaluated
          exact Or.inr ⟨channels, prepared, raw, afterOperands, afterMaterialized, setup, produced, materialized, released, rfl⟩

#print axioms withExitChannels_escape_origin
#print axioms returnFromForward_escape_produce_origin

end Goose.Proofs.ExitExecution
