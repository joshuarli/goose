import Goose.Proofs.ConstructionExecutionProtocolNamedReservationRestore
import Goose.Proofs.ConstructionExecutionProtocolNamedReservationChildren
import Lean.Meta.Tactic.Delta

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev commitLookup (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

theorem namedReservationCommit_lookup (id : DestinationId) (state : ConstructionState) :
    commitLookup id state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state := lookupDestination_result id state

def namedReservationCommit (token : ExitReservationId) (incoming selected : DestinationId)
    (snapshot : PendingDestination) : ConstructionM DestinationId := do
  restoreNamedDestination selected
  let parent ← commitLookup selected
  if {parent with progress := snapshot.progress} != snapshot then ConstructionM.fail .ownership
  let .built count := snapshot.progress | ConstructionM.fail .protocol
  namedReservationChildren selected parent count
  namedReservationFinish token incoming selected snapshot

private def namedReservationDispatch (token : ExitReservationId) : ConstructionM DestinationId := fun state =>
  match state.exitReservations[token]? with
  | some (.active (.named .ready) incoming selected snapshot) =>
    namedReservationCommit token incoming selected snapshot state
  | _ => .fault .protocol state

local syntax "named_materialize_active" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_active) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      return [← goal.deltaTarget fun name => Lean.privateToUserName name == `Goose.Construct.active]

local syntax "named_materialize_split_if" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal none true
        | Lean.throwError "no named materialization condition to split"
      return [yes.mvarId, no.mvarId]

local syntax "named_materialize_split" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_split) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some goals ← Lean.Meta.splitTarget? goal true true
        | Lean.throwError "no named materialization branch to split"
      return goals

local syntax "named_materialize_progress" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_progress) => Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← goal.getType
      let some progress := target.find? fun expression =>
          expression.isAppOfArity ``PendingDestination.progress 1 && !expression.hasLooseBVars
        | Lean.throwError "no named materialization progress to split"
      let (_, variables, next) ← goal.generalizeHyp #[{expr := progress, hName? := some `sourceProgress}] (← Lean.getLCtx).getFVarIds
      let branches ← next.cases variables[0]!
      return branches.toList.map (·.mvarId)

local syntax "named_materialize_data" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_data) => Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← goal.getType
      let some value := target.find? fun expression =>
          !expression.hasLooseBVars &&
            (expression.isAppOfArity ``destinationCurrent 2 ||
              expression.isAppOfArity ``GetElem?.getElem? 7)
        | Lean.throwError "no named materialization data to split"
      let (_, variables, next) ← goal.generalizeHyp #[{expr := value, hName? := some `sourceRead}] (← Lean.getLCtx).getFVarIds
      let branches ← next.cases variables[0]!
      return branches.toList.map (·.mvarId)

local syntax "named_materialize_backing" : tactic
elab_rules : tactic
  | `(tactic| named_materialize_backing) => Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← goal.getType
      let some value := target.find? fun expression =>
          !expression.hasLooseBVars &&
            expression.isAppOfArity ``PendingDestination.backing 1
        | Lean.throwError "no named materialization data to split"
      let (_, variables, next) ← goal.generalizeHyp #[{expr := value, hName? := some `sourceRead}] (← Lean.getLCtx).getFVarIds
      let branches ← next.cases variables[0]!
      return branches.toList.map (·.mvarId)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
private theorem materializeNamedReservation_dispatch (token : ExitReservationId) :
    materializeNamedReservation token = namedReservationDispatch token := by
  funext state
  simp only [materializeNamedReservation, namedReservationDispatch, ConstructionM.get, bind]
  named_materialize_active
  cases ticket : state.exitReservations[token]? with
  | none => rfl
  | some reservation =>
    cases reservation with
    | waiting incoming | restored | released => rfl
    | active role incoming selected snapshot =>
      cases role with
      | fresh => rfl
      | named stage =>
        cases stage with
        | awaitingSource | materialized => rfl
        | ready =>
          cases snapshotProgress : snapshot.progress <;>
            simp only [snapshotProgress, pure, bind, namedReservationCommit, namedReservationChildren, namedReservationFinish,
            namedReservationReadStorage, namedReservationWriteDestination, namedReservationReadDestination,
            namedReservationChildStorage, namedReservationActive, commitLookup, lookupDestination_result, lookupStorage_result, replaceDestination_result,
            ConstructionM.get, ConstructionM.set, ConstructionM.fail]
          all_goals dsimp
          all_goals try simp only [lookupDestination_result, lookupStorage_result, replaceDestination_result,
            bind, pure, ConstructionM.get, ConstructionM.set, ConstructionM.fail]
          all_goals repeat' first
            | rfl
            | (named_materialize_progress <;> try dsimp <;> try simp_all only [bind, pure, ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                ConstructionResult.ok.injEq, ConstructionResult.fault.injEq, Option.some.injEq, reduceCtorEq])
            | (named_materialize_data <;> try dsimp <;> try simp_all only [bind, pure, ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                ConstructionResult.ok.injEq, ConstructionResult.fault.injEq, Option.some.injEq, reduceCtorEq])
            | (named_materialize_split <;> try dsimp <;> try simp_all only [bind, pure, ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                ConstructionResult.ok.injEq, ConstructionResult.fault.injEq, Option.some.injEq, reduceCtorEq])
            | (named_materialize_split_if <;> try dsimp <;>
                try simp_all only [bind, pure, ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                ConstructionResult.ok.injEq, ConstructionResult.fault.injEq, Option.some.injEq, reduceCtorEq])            | (named_materialize_backing <;> try dsimp <;> try simp_all only [bind, pure,
                ConstructionM.get, ConstructionM.set, ConstructionM.fail, ConstructionResult.ok.injEq,
                ConstructionResult.fault.injEq, Option.some.injEq, reduceCtorEq])




theorem materializeNamedReservation_result (token : ExitReservationId) (state : ConstructionState) :
    materializeNamedReservation token state = match state.exitReservations[token]? with
      | some (.active (.named .ready) incoming selected snapshot) =>
        namedReservationCommit token incoming selected snapshot state
      | _ => .fault .protocol state := by
  rw [materializeNamedReservation_dispatch]
  rfl

private theorem namedReservationCommit_lifecycle (token : ExitReservationId) (incoming selected : DestinationId)
    (snapshot : PendingDestination) (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (namedReservationCommit token incoming selected snapshot state).finalState := by
  simp only [namedReservationCommit, bind]
  have cleanedValid := restoreNamedDestination_lifecycle selected state valid
  cases cleaned : restoreNamedDestination selected state with
  | fault kind after =>
    simpa only [cleaned, bind, ConstructionResult.finalState] using cleanedValid
  | ok ignored after =>
    cases ignored
    simp only [cleaned, ConstructionResult.finalState] at cleanedValid
    simp only [cleaned, bind, commitLookup, lookupDestination_result]
    cases present : after.destinations[selected]? with
    | none => exact cleanedValid
    | some parent =>
      simp only [present]
      named_materialize_split_if
      · exact cleanedValid
      · rename_i guard
        have normalized : {parent with progress := snapshot.progress} = snapshot := by
          apply Classical.byContradiction
          intro different
          exact guard (by simp [different])
        cases snapshotProgress : snapshot.progress <;> simp only [snapshotProgress] <;> try exact cleanedValid
        case built count =>
          have preserved := namedReservationChildren_lifecycle selected parent count after present cleanedValid
          cases prepared : namedReservationChildren selected parent count after with
          | fault reason finalState =>
            simpa only [prepared, bind, ConstructionResult.finalState] using preserved.1
          | ok ignored finalState =>
            cases ignored
            simp only [prepared, ConstructionResult.finalState] at preserved
            have mutable := namedReservationChildren_success_progress selected parent count after finalState prepared
            have completed := namedReservationFinish_lifecycle token incoming selected snapshot parent count finalState
              preserved.2 (by simpa only [snapshotProgress] using normalized) mutable preserved.1
            simpa only [prepared, bind] using completed

theorem materializeNamedReservation_lifecycle (token : ExitReservationId) (state : ConstructionState)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (materializeNamedReservation token state).finalState := by
  rw [materializeNamedReservation_dispatch]
  unfold namedReservationDispatch
  cases ticket : state.exitReservations[token]? with
  | none => exact valid
  | some reservation =>
    cases reservation with
    | waiting incoming | restored | released => exact valid
    | active role incoming selected snapshot =>
      cases role with
      | fresh => exact valid
      | named stage =>
        cases stage with
        | awaitingSource | materialized => exact valid
        | ready => exact namedReservationCommit_lifecycle token incoming selected snapshot state valid

end Goose.Proofs.ConstructionExecutionProtocol
