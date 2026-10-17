import Goose.Proofs.ConstructionExecutionOwnershipEvaluationCombinators
import Goose.Proofs.ConstructionExecutionOwnershipLiveFreshRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

def OwnershipSourceAmbientInvariant (state : ConstructionState) (ambient : OwnershipAmbient) : Prop :=
  OwnershipAmbientInvariant state ambient ∧ DestinationSuccessorsValid state ∧ LiveFreshReservationRawRoles state

def OwnershipSourceOutcome (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) : Prop :=
  OwnershipAmbientOutcome ambient shape result ∧
    DestinationSuccessorsValid (Goose.Proofs.Exit.stepState result).construction ∧
    LiveFreshReservationRawRoles (Goose.Proofs.Exit.stepState result).construction

abbrev PreservesOwnershipSourceAmbient (shape : OwnershipResultShape α) (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (ambient : OwnershipAmbient),
    OwnershipSourceAmbientInvariant state.construction ambient → OwnershipSourceOutcome ambient shape (action state)

theorem ownershipSourceAmbientInvariant_structural (state : ConstructionState) (ambient : OwnershipAmbient)
    (valid : OwnershipSourceAmbientInvariant state ambient) : OwnershipSourceStructural state :=
  ⟨valid.1.structural, valid.2⟩

theorem ownershipSourceOutcome_structural (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) (valid : OwnershipSourceOutcome ambient shape result) :
    OwnershipSourceStructural (Goose.Proofs.Exit.stepState result).construction := by
  refine ⟨?_, valid.2⟩
  cases result with
  | ok value state | escape address carriers state => exact valid.1.structural
  | stop reason state => exact valid.1
  | jump target kind state => cases kind <;> exact valid.1.structural

theorem initial_ownershipSourceAmbientInvariant : OwnershipSourceAmbientInvariant .initial [] :=
  ⟨initial_ownershipAmbientInvariant, initial_destination_successors, initial_liveFreshReservationRawRoles⟩

theorem ownershipSource_pure (shape : OwnershipResultShape α) (value : α) :
    PreservesOwnershipSourceAmbient shape (pure value) := by
  intro state ambient valid
  exact ⟨ownershipAmbient_pure shape value state ambient valid.1, valid.2⟩

theorem ownershipSource_stop (shape : OwnershipResultShape α) (reason : Goose.Core.Stop) :
    PreservesOwnershipSourceAmbient shape (EvalM.stop reason) := by
  intro state ambient valid
  exact ⟨valid.1.structural, valid.2⟩

theorem ownershipSource_stateQuery (shape : OwnershipResultShape α) (action : EvalM α)
    (query : Goose.Proofs.ConstructionExecutionProtocol.StateQuery action) :
    PreservesOwnershipSourceAmbient shape action := by
  intro state ambient valid
  refine ⟨ownershipAmbient_stateQuery shape action query state ambient valid.1, ?_⟩
  simpa only [query state] using valid.2

theorem ownershipSource_bind_none (action : EvalM α) (next : α → EvalM β)
    (shape : OwnershipResultShape β) (first : PreservesOwnershipSourceAmbient .none action)
    (remaining : ∀ value, PreservesOwnershipSourceAmbient shape (next value)) :
    PreservesOwnershipSourceAmbient shape (action >>= next) := by
  intro state ambient valid
  have firstValid := first state ambient valid
  cases result : action state with
  | ok value after =>
      simp only [bind, result]
      simp only [OwnershipSourceOutcome, result, OwnershipAmbientOutcome,
        OwnershipResultShape.retainedCarriers, Goose.Proofs.Exit.stepState] at firstValid
      exact remaining value after ambient
        ⟨(ownershipAmbientInvariant_returned_nil after.construction ambient).mp firstValid.1, firstValid.2⟩
  | stop reason after =>
      simpa only [OwnershipSourceOutcome, bind, result, OwnershipAmbientOutcome,
        Goose.Proofs.Exit.stepState] using firstValid
  | escape address carriers after =>
      simpa only [OwnershipSourceOutcome, bind, result, OwnershipAmbientOutcome,
        Goose.Proofs.Exit.stepState] using firstValid
  | jump target kind after =>
      cases kind <;> simpa only [OwnershipSourceOutcome, bind, result, OwnershipAmbientOutcome,
        Goose.Proofs.Exit.stepState] using firstValid

theorem evaluation_zero_source_ownership (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction 0 config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipSourceAmbientInvariant state.construction ambient) :
    OwnershipSourceOutcome ambient shape (action state) := by
  refine ⟨evaluation_zero_ownership config shape action actual state ambient valid.1, ?_⟩
  cases actual <;>
    simpa only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
      buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
      execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
      execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
      Goose.Proofs.Exit.stepState] using valid.2

end Goose.Proofs.ConstructionExecutionOwnership
