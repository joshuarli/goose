import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionCleanupFrames
import Goose.Proofs.ExitExecutionInvocationStatementsCausalWitness

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def unwindFrameValue (state : ExecutionState) :=
  (state.objects, state.construction.stdout)

private abbrev KeepsUnwindFrame (action : EvalM α) : Prop :=
  ∀ state, unwindFrameValue (Goose.Proofs.Exit.stepState (action state)) = unwindFrameValue state

private theorem keepsUnwindFrame_query (action : EvalM α) (query : StateQuery action) :
    KeepsUnwindFrame action := by
  intro state
  rw [query state]

private theorem keepsUnwindFrame_bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsUnwindFrame action) (remaining : ∀ value, KeepsUnwindFrame (next value)) :
    KeepsUnwindFrame (action >>= next) :=
  Goose.Proofs.Exit.runtime_bind_frames unwindFrameValue action next first remaining

private theorem restoreCompletedOwner_unwind_frame (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    KeepsUnwindFrame (restoreCompletedOwner snapshot incoming carried) := by
  unfold restoreCompletedOwner
  cases snapshot.progress with
  | built originalCount =>
      apply keepsUnwindFrame_bind
      · exact keepsUnwindFrame_query _ (stateQuery_receivingDestination _)
      · intro current
        apply keepsUnwindFrame_bind
        · exact keepsUnwindFrame_query _ stateQuery_get
        · intro state
          split
          · exact keepsUnwindFrame_query _ (stateQuery_pure _)
          ·
            apply keepsUnwindFrame_bind
            · exact keepsUnwindFrame_query _ (stateQuery_getDestination current)
            · intro child
              apply keepsUnwindFrame_bind
              · exact keepsUnwindFrame_query _ (stateQuery_getDestination snapshot.capability.id)
              · intro parent
                cases parent.progress with
                | suspended count expected =>
                    cases child.progress with
                    | abandoned | cancelled =>
                        cases countInvalid : (count != originalCount) with
                        | true => simp [countInvalid]; exact keepsUnwindFrame_query _ (fun _ => rfl)
                        | false =>
                          cases ownerInvalid : (expected != current) with
                          | true => simp [countInvalid, ownerInvalid]; exact keepsUnwindFrame_query _ (fun _ => rfl)
                          | false =>
                            cases childInvalid : (child.use != .child snapshot.capability.id) with
                            | true =>
                                simp [countInvalid, ownerInvalid]
                                exact keepsUnwindFrame_query _ (fun _ => rfl)
                            | false =>
                              cases parentInvalid :
                                  ({ parent with progress := .built originalCount } != snapshot) with
                              | true =>
                                  simp [countInvalid, ownerInvalid]
                                  exact keepsUnwindFrame_query _ (fun _ => rfl)
                              | false =>
                                simp [countInvalid, ownerInvalid]
                                intro currentState
                                rfl
                    | _ => exact keepsUnwindFrame_query _ (stateQuery_pure _)
                | _ => exact keepsUnwindFrame_query _ (stateQuery_pure _)
  | _ => exact keepsUnwindFrame_query _ (fun _ => rfl)


private theorem ownerEscape_unwind_frame {α : Type} (snapshot : Option PendingDestination) (destination : Nat)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState) :
    unwindFrameValue (Goose.Proofs.Exit.stepState
      (match snapshot with
      | none => ExecutionStep.escape (α := α) address carriers before
      | some parent => match restoreCompletedOwner parent destination
          (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before with
        | .ok () final => .escape address carriers final
        | .stop reason final => .stop reason final
        | .escape target payload final => .escape target payload final
        | .jump target kind final => .jump target kind final)) = unwindFrameValue before := by
  cases snapshot with
  | none => rfl
  | some parent =>
      have frame := restoreCompletedOwner_unwind_frame parent destination
        (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before
      cases restored : restoreCompletedOwner parent destination
          (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before <;>
        simpa only [restored, Goose.Proofs.Exit.stepState] using frame


private theorem StatementInvocationUnwinds.unwind_frame {config : EvalConfig}
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    {edge : StatementInvocationEdge config parent initial child prepared} {outcome : ExecutionStep α}
    (unwinds : StatementInvocationUnwinds config address carriers before edge outcome) :
    unwindFrameValue (Goose.Proofs.Exit.stepState outcome) = unwindFrameValue before := by
  cases unwinds <;> subst_vars <;> try rfl
  all_goals exact ownerEscape_unwind_frame _ _ _ _ _


theorem restoreCompletedOwner_frame (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) (initial : ExecutionState) :
    let final := Goose.Proofs.Exit.stepState (restoreCompletedOwner snapshot incoming carried initial)
    final.construction.stdout = initial.construction.stdout ∧ final.objects = initial.objects := by
  have frame := restoreCompletedOwner_unwind_frame snapshot incoming carried initial
  exact ⟨congrArg Prod.snd frame, congrArg Prod.fst frame⟩

theorem StatementInvocationUnwinds.frame {config : EvalConfig}
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    {edge : StatementInvocationEdge config parent initial child prepared} {outcome : ExecutionStep α}
    (unwinds : StatementInvocationUnwinds config address carriers before edge outcome) :
    let final := Goose.Proofs.Exit.stepState outcome
    final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  have frame := unwinds.unwind_frame
  exact ⟨congrArg Prod.snd frame, congrArg Prod.fst frame⟩

theorem statementInvocation_escape_frame (config : EvalConfig)
    {α : Type} (parent : ExitInvocation α) (source : StatementInvocationSource parent)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : parent.action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      StatementInvocationEdge config parent initial child prepared ∧
      child.action config prepared = .escape address carriers before ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨β, child, prepared, before, edge, evaluated, unwinds⟩ :=
    statementInvocation_escape_cause config parent source initial final address carriers escaped
  obtain ⟨stdout, objects⟩ := unwinds.frame
  exact ⟨β, child, prepared, before, edge, evaluated, stdout, objects⟩

theorem ExitReached.statementSource_escape_frame {rootFuel : Nat} {config : EvalConfig}
    {α : Type} {parent : ExitInvocation α} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config parent initial) (source : StatementInvocationSource parent)
    (escaped : parent.action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      StatementInvocationEdge config parent initial child prepared ∧
      child.action config prepared = .escape address carriers before ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨β, child, prepared, before, edge, evaluated, stdout, objects⟩ :=
    statementInvocation_escape_frame config parent source initial final address carriers escaped
  exact ⟨β, child, prepared, before, .call reached (.statements edge), edge, evaluated, stdout, objects⟩

#print axioms restoreCompletedOwner_frame
#print axioms StatementInvocationUnwinds.frame
#print axioms statementInvocation_escape_frame
#print axioms ExitReached.statementSource_escape_frame

end Goose.Proofs.ExitExecution
