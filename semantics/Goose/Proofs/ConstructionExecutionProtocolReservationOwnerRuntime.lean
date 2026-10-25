import Goose.Proofs.ConstructionExecutionProtocolReservationOwnerRestore
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Goose.Proofs.ConstructionExecutionProtocolExecutionKernel
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "owner_split_if" : tactic
elab_rules : tactic
  | `(tactic| owner_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal | Lean.throwError "no owner condition to split"
      return [yes.mvarId, no.mvarId]

theorem restoreCompletedOwner_reservation_lifecycle (snapshot : PendingDestination)
    (incoming : DestinationId) (carried : List DestinationId) :
    PreservesConstructionInvariant ReservationLifecycleInvariant (restoreCompletedOwner snapshot incoming carried) := by
  intro state valid
  simp only [restoreCompletedOwner]
  cases progress : snapshot.progress <;> try exact valid
  rename_i originalCount
  have receiving := stateQuery_receivingDestination incoming state
  cases resolved : receivingDestination incoming state with
  | stop reason after | escape target carriers after | jump target kind after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at receiving
      simpa only [resolved, bind, Goose.Proofs.Exit.stepState, receiving] using valid
  | ok current after =>
      simp only [resolved, Goose.Proofs.Exit.stepState] at receiving
      subst after
      simp only [resolved, bind, EvalM.get]
      split
      · exact valid
      · cases childFound : state.construction.destinations[current]? with
        | none => simpa only [getDestination, EvalM.get, bind, childFound, Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState] using valid
        | some child =>
            cases parentFound : state.construction.destinations[snapshot.capability.id]? with
            | none => simpa only [getDestination, EvalM.get, bind, childFound, pure, parentFound, Construct.fault, EvalM.stop, Goose.Proofs.Exit.stepState] using valid
            | some parent =>
                simp only [getDestination, EvalM.get, bind, childFound, parentFound, pure]
                cases parentProgress : parent.progress <;> cases childProgress : child.progress <;>
                  try exact valid
                all_goals
                  rename_i count expected
                  simp only []
                  owner_split_if
                  · simpa only [Construct.fault, EvalM.stop, bind, Goose.Proofs.Exit.stepState] using valid
                  · rename_i guard
                    have same : {parent with progress := .built originalCount} = snapshot := by
                      apply Classical.byContradiction
                      intro different
                      exact guard (by simp [different])
                    have countEqual : count = originalCount := by
                      apply Classical.byContradiction
                      intro different
                      exact guard (by simp [different])
                    simp only [EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]
                    have restored : snapshot = {parent with progress := .built originalCount} := by
                      simpa only [progress] using same.symm
                    have fixed := reservationLifecycleInvariant_restore_completed_owner state.construction
                      snapshot.capability.id parent originalCount expected parentFound
                      (by simpa only [countEqual] using parentProgress) valid
                    simpa only [ExecutionInvariant, ←restored] using fixed

end Goose.Proofs.ConstructionExecutionProtocol
