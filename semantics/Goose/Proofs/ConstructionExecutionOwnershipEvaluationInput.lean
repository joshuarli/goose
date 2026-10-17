import Goose.Proofs.ConstructionExecutionOwnershipEvaluationSourceContext
import Goose.Proofs.OwnershipAmbientTicketScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

structure OwnershipEvaluationInput (state : ExecutionState) (ambient : OwnershipAmbient) : Prop where
  source : OwnershipSourceAmbientInvariant state.construction ambient
  runtime : OwnershipRuntimeFrames state ambient
  reservations : OwnershipReservationFrames state.construction ambient

def OwnershipEvaluationFrameOutcome (ambient : OwnershipAmbient) : ExecutionStep α → Prop
  | .stop _ _ => True
  | .ok _ state | .escape _ _ state | .jump _ _ state =>
      OwnershipRuntimeFrames state ambient ∧ OwnershipReservationFrames state.construction ambient

def OwnershipEvaluationOutcome (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) : Prop :=
  OwnershipSourceOutcome ambient shape result ∧ OwnershipEvaluationFrameOutcome ambient result

abbrev PreservesOwnershipEvaluationInput (shape : OwnershipResultShape α) (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (ambient : OwnershipAmbient),
    OwnershipEvaluationInput state ambient → OwnershipEvaluationOutcome ambient shape (action state)

theorem initial_ownershipEvaluationInput : OwnershipEvaluationInput .initial [] :=
  ⟨initial_ownershipSourceAmbientInvariant, initial_ownershipRuntimeFrames, initial_ownershipReservationFrames⟩

theorem ownershipEvaluationInput_returned (state : ExecutionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) (valid : OwnershipEvaluationInput state ambient) :
    OwnershipEvaluationInput state (.returned carriers :: ambient) := by
  refine ⟨⟨ownershipAmbientInvariant_returned state.construction ambient carriers valid.source.1,
    valid.source.2⟩, ?_, ?_⟩
  · exact (ownershipRuntimeFrames_returned state ambient carriers).mpr valid.runtime
  · exact (ownershipReservationFrames_returned state.construction ambient carriers).mpr valid.reservations

theorem ownershipEvaluationInput_returned_nil (state : ExecutionState) (ambient : OwnershipAmbient) :
    OwnershipEvaluationInput state (.returned [] :: ambient) ↔ OwnershipEvaluationInput state ambient := by
  constructor
  · intro valid
    refine ⟨⟨(ownershipAmbientInvariant_returned_nil state.construction ambient).mp valid.source.1,
      valid.source.2⟩, ?_, ?_⟩
    · exact (ownershipRuntimeFrames_returned state ambient []).mp valid.runtime
    · exact (ownershipReservationFrames_returned state.construction ambient []).mp valid.reservations
  · exact ownershipEvaluationInput_returned state ambient []

theorem ownershipEvaluation_pure (shape : OwnershipResultShape α) (value : α) :
    PreservesOwnershipEvaluationInput shape (pure value) := by
  intro state ambient valid
  exact ⟨ownershipSource_pure shape value state ambient valid.source, valid.runtime, valid.reservations⟩

theorem ownershipEvaluation_stop (shape : OwnershipResultShape α) (reason : Goose.Core.Stop) :
    PreservesOwnershipEvaluationInput shape (EvalM.stop reason) := by
  intro state ambient valid
  exact ⟨ownershipSource_stop shape reason state ambient valid.source, True.intro⟩

theorem ownershipEvaluation_stateQuery (shape : OwnershipResultShape α) (action : EvalM α)
    (query : Goose.Proofs.ConstructionExecutionProtocol.StateQuery action) :
    PreservesOwnershipEvaluationInput shape action := by
  intro state ambient valid
  refine ⟨ownershipSource_stateQuery shape action query state ambient valid.source, ?_⟩
  have final := query state
  cases result : action state with
  | stop reason after => trivial
  | ok value after | escape address carriers after | jump target kind after =>
      simp only [result, Goose.Proofs.Exit.stepState] at final
      subst after
      exact ⟨valid.runtime, valid.reservations⟩

theorem ownershipEvaluation_bind_none (action : EvalM α) (next : α → EvalM β)
    (shape : OwnershipResultShape β) (first : PreservesOwnershipEvaluationInput .none action)
    (remaining : ∀ value, PreservesOwnershipEvaluationInput shape (next value)) :
    PreservesOwnershipEvaluationInput shape (action >>= next) := by
  intro state ambient valid
  have firstValid := first state ambient valid
  cases result : action state with
  | ok value after =>
      simp only [OwnershipEvaluationOutcome, OwnershipSourceOutcome, result, OwnershipAmbientOutcome,
        OwnershipResultShape.retainedCarriers, Goose.Proofs.Exit.stepState,
        OwnershipEvaluationFrameOutcome] at firstValid
      have afterValid : OwnershipEvaluationInput after ambient :=
        ⟨⟨(ownershipAmbientInvariant_returned_nil after.construction ambient).mp firstValid.1.1,
          firstValid.1.2⟩, firstValid.2.1, firstValid.2.2⟩
      simpa only [bind, result] using remaining value after ambient afterValid
  | stop reason after =>
      simpa only [OwnershipEvaluationOutcome, OwnershipSourceOutcome, bind, result,
        OwnershipAmbientOutcome, OwnershipEvaluationFrameOutcome, Goose.Proofs.Exit.stepState] using firstValid
  | escape address carriers after =>
      simpa only [OwnershipEvaluationOutcome, OwnershipSourceOutcome, bind, result,
        OwnershipAmbientOutcome, OwnershipEvaluationFrameOutcome, Goose.Proofs.Exit.stepState] using firstValid
  | jump target kind after =>
      cases kind <;> simpa only [OwnershipEvaluationOutcome, OwnershipSourceOutcome, bind, result,
        OwnershipAmbientOutcome, OwnershipEvaluationFrameOutcome, Goose.Proofs.Exit.stepState] using firstValid

theorem evaluation_zero_input_ownership (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction 0 config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient) (valid : OwnershipEvaluationInput state ambient) :
    OwnershipEvaluationOutcome ambient shape (action state) := by
  refine ⟨evaluation_zero_source_ownership config shape action actual state ambient valid.source, ?_⟩
  cases actual <;>
    simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
      buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
      execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
      execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
      OwnershipEvaluationFrameOutcome]

end Goose.Proofs.ConstructionExecutionOwnership
