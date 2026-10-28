import Goose.Proofs.ConstructionExitTargetByteReadiness
import Goose.Proofs.ConstructionExitCheckpointEntryTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveReturnCleaned : ExecutionState :=
  Goose.Proofs.Exit.stepState (execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource
    (.returnFrom 0 [.bytes array [66] 0] 0) recursiveDirectCheckpoint)

def recursiveReturnAmbient : OwnershipAmbient := .returned [.completed 1] :: recursiveCheckpointAmbient

def recursiveReturnPending : List PendingCarrierFrame := [⟨[.construct 1], [.completed 1]⟩]

theorem recursive_return_source_and_carrier :
    OwnershipSourceState recursiveReturnCleaned.construction ∧
    CarriersLandingReady recursiveReturnCleaned [.construct 1] [.completed 1] ∧
    CarrierResultBacking recursiveCheckpointConfig.layout recursiveReturnCleaned (.completed 1) ∧
    EvaluationHistoryLifecycle recursiveReturnCleaned recursiveReturnAmbient recursiveReturnPending := by
  have selection : targetActivation recursiveCheckpointConfig 0 recursiveDirectCheckpoint = .ok recursiveCheckpointTarget recursiveDirectCheckpoint := by cbv
  have current : destinationCurrent recursiveDirectCheckpoint.construction 1 = .ok 1 := by cbv
  obtain ⟨after, escaped, paired, backed, _, source, history⟩ := checked_byte_returnFrom_target 0 recursiveCheckpointConfig 0
    recursiveCheckpointSource recursiveCheckpointTarget 0 1 [66] 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
    recursiveCheckpointTypes recursiveCheckpointLive [] [] recursive_checkpoint_world recursive_checkpoint_ambient_history
    recursiveCheckpointBacking selection rfl rfl rfl rfl rfl current (by decide)
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! recursiveDirectCheckpoint.construction.exitReservations.size .released } }
  have stateEq : recursiveReturnCleaned = cleaned := by
    simp only [recursiveReturnCleaned, array, escaped, Goose.Proofs.Exit.stepState]
    rfl
  change CarriersLandingReady cleaned [.construct 1] [.completed 1] at paired
  change EvaluationHistoryLifecycle cleaned recursiveReturnAmbient recursiveReturnPending at history
  change CarrierResultBacking recursiveCheckpointConfig.layout cleaned (.completed 1) at backed
  change OwnershipSourceState cleaned.construction at source
  rw [stateEq]
  exact ⟨source, paired, backed, history⟩

theorem recursive_return_tables :
    recursiveReturnCleaned.construction.exitReservations = #[.released] ∧
    recursiveReturnCleaned.construction.destinations.size = 2 := by cbv

theorem recursive_return_active_rows (id : Nat) (row : PendingDestination)
    (present : recursiveReturnCleaned.construction.destinations[id]? = some row) :
    activeProgress row.progress = true := by
  have bound := (Array.getElem?_eq_some_iff.mp present).1
  rw [recursive_return_tables.2] at bound
  have idCase : id = 0 ∨ id = 1 := by omega
  rcases idCase with zero | one <;> subst id <;> cbv at present <;> cases present <;> rfl

theorem recursive_return_execution_context : OwnershipExecutionContext recursiveReturnCleaned recursiveReturnAmbient := by
  have source := recursive_return_source_and_carrier.1
  refine ⟨source, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨source.structural.1, ?_, ?_⟩
    · intro id row found inactive supported
      have active := recursive_return_active_rows id row found
      rw [active] at inactive
      cases inactive
    · cbv
      simp
  · constructor <;> cbv
  · intro token reservation present needed
    rw [recursive_return_tables.1] at present
    cases token with
    | zero =>
      simp at present
      subst reservation
      cases needed
    | succ token => simp at present
  · cbv
    simp [OwnershipChannelReceivingWithinFrames, OwnershipReceivingWithinSuccessorFrames, OwnershipAmbientFrame.tickets]
  · cbv
    simp [OwnershipChannelReceivingBound]
  · constructor <;> cbv <;> simp

theorem recursive_return_runtime_frame :
    recursiveReturnCleaned.objects = recursiveDirectCheckpoint.objects ∧
    recursiveReturnCleaned.objectOrdinals = recursiveDirectCheckpoint.objectOrdinals ∧
    recursiveReturnCleaned.nextAct = recursiveDirectCheckpoint.nextAct ∧
    recursiveReturnCleaned.nextScope = recursiveDirectCheckpoint.nextScope := by cbv

theorem recursive_return_accepted_world :
    AcceptedWorld recursiveCheckpointConfig 0 recursiveReturnCleaned recursiveReturnAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [] recursiveReturnPending := by
  have previous := recursive_checkpoint_world
  have runtime := recursive_return_runtime_frame
  refine ⟨⟨recursive_return_execution_context, ?_, previous.globalTypes, previous.layouts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, previous.globalLive⟩
  · exact ⟨previous.globals.1, by intro id bound; omega⟩
  · intro act scope id ty declared
    simpa only [runtime.2.2.1, runtime.2.2.2] using previous.typeFrontier act scope id ty declared
  · intro id ty declared outside
    simpa only [runtime.2.2.2, recursiveCheckpointConfig] using previous.syntheticFrontier id ty declared outside
  · intro root ty value declared found
    exact previous.heap root ty value declared (by simpa only [runtime.1] using found)
  · intro root value found
    exact previous.objectsRegistered root value (by simpa only [runtime.1] using found)
  · intro root ordinal found
    exact previous.ordinalsRegistered root ordinal (by simpa only [runtime.2.1] using found)
  · refine ⟨?_, ?_⟩
    · intro root active value found
      rcases active with same | same <;> subst root <;> cbv at found <;> cases found <;> exact .integer _ _
    · intro root active stored found
      rcases active with same | same <;> subst root <;> cbv at found <;> cases found
  · intro region member
    cases member
  · intro frame member
    simp only [recursiveReturnPending, List.mem_singleton] at member
    subst frame
    refine ⟨recursive_return_source_and_carrier.2.1, ?_⟩
    intro carrier present
    simp only [List.mem_singleton] at present
    subst carrier
    exact recursive_return_source_and_carrier.2.2.1

theorem recursive_return_execution :
    execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)
      recursiveDirectCheckpoint = .escape ⟨2, .nonlocal 0⟩ [.completed 1] recursiveReturnCleaned := by
  obtain ⟨after, escaped, _, _⟩ := recursive_checkpoint_direct_return
  have stateEq : recursiveReturnCleaned = { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! 0 .released } } := by
    simp only [recursiveReturnCleaned, array, escaped, Goose.Proofs.Exit.stepState]
  simpa only [array, stateEq] using escaped

theorem validated_recursive_return_post_world :
    validate recursiveDestinations = .ok () ∧
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    ExitReached 32 recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint ∧
    execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)
      recursiveDirectCheckpoint = .escape ⟨2, .nonlocal 0⟩ [.completed 1] recursiveReturnCleaned ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveReturnCleaned recursiveReturnAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [] recursiveReturnPending ∧
    EvaluationHistoryLifecycle recursiveReturnCleaned recursiveReturnAmbient recursiveReturnPending ∧
    CarriersLandingReady recursiveReturnCleaned [.construct 1] [.completed 1] ∧
    CarrierResultBacking recursiveCheckpointConfig.layout recursiveReturnCleaned (.completed 1) :=
  ⟨validated_recursive_direct_return.1, recursive_successful_run_execution.1, recursive_successful_run_reaches_return,
    recursive_return_execution, recursive_return_accepted_world, recursive_return_source_and_carrier.2.2.2,
    recursive_return_source_and_carrier.2.1, recursive_return_source_and_carrier.2.2.1⟩

#print axioms validated_recursive_return_post_world
#print axioms recursive_return_execution

#print axioms recursive_return_accepted_world

#print axioms recursive_return_execution_context

#print axioms recursive_return_source_and_carrier

end Goose.Proofs.ConstructionAcceptedExecution
