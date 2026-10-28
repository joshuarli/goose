import Goose.Proofs.ConstructionAcceptedTwoArgumentExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

inductive StatefulScalarValues : List (Expr × Ty) → List Value → Prop
  | nil : StatefulScalarValues [] []
  | cons {specification : Expr × Ty} {value : Value} {specifications : List (Expr × Ty)} {values : List Value}
      (represented : ValueRepresentation specification.2 value) (tail : StatefulScalarValues specifications values) :
      StatefulScalarValues (specification :: specifications) (value :: values)

theorem evalArguments_statefulScalarList_world (specifications : List (Expr × Ty)) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
      (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (variables : Array LocalVar) (parameters : List Param),
      parameters.length = specifications.length →
      AcceptedWorld config frame.initialized state ambient types live regions pending →
      AcceptedFrame config accepted frame state types →
      (∀ specification ∈ specifications, ∀ runtimeFuel current,
        AcceptedWorld config frame.initialized current ambient types live regions pending →
        AcceptedFrame config accepted frame current types →
        FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
          (evalValue runtimeFuel config frame.interpretation.environment specification.1 current)) →
      let step := evalArguments fuel config frame.interpretation.environment variables parameters
        (specifications.map fun specification => .byVal specification.1) state
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState step) types ∧
      match step with
      | .ok values _ => StatefulScalarValues specifications values
      | .stop .. => True
      | _ => False := by
  induction specifications with
  | nil =>
    intro fuel config accepted frame state ambient types live regions pending variables parameters lengths world source safe
    cases parameters with
    | cons first rest => simp at lengths
    | nil =>
      cases fuel <;> simp [evalArguments, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState, world, source, StatefulScalarValues.nil]
  | cons specification rest ih =>
    intro fuel config accepted frame state ambient types live regions pending variables parameters lengths world source safe
    cases parameters with
    | nil => simp at lengths
    | cons first tail =>
      have restLengths : tail.length = rest.length := by simpa using lengths
      cases fuel with
      | zero => simp [evalArguments, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
      | succ fuel =>
        have firstSafe := safe specification (by simp) fuel state world source
        cases evaluated : evalValue fuel config frame.interpretation.environment specification.1 state with
        | escape address carriers after | jump target kind after => simp [evaluated, FirstArgumentOutcome] at firstSafe
        | stop reason after =>
          simpa [evalArguments, bind, evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using firstSafe
        | ok value middle =>
          simp only [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] at firstSafe
          have tailSafe := ih fuel config accepted frame middle ambient types live regions pending variables tail restLengths
            firstSafe.1 firstSafe.2.1 (by intro item member; exact safe item (by simp [member]))
          cases remaining : evalArguments fuel config frame.interpretation.environment variables tail
              (rest.map fun item => .byVal item.1) middle with
          | escape address carriers after | jump target kind after => simp [remaining] at tailSafe
          | stop reason after =>
            simpa [evalArguments, bind, pure, evaluated, remaining, Goose.Proofs.Exit.stepState] using tailSafe
          | ok values after =>
            simp only [remaining, Goose.Proofs.Exit.stepState] at tailSafe
            simp only [List.map_cons, evalArguments, bind, evaluated, remaining, pure, Goose.Proofs.Exit.stepState]
            exact ⟨tailSafe.1, tailSafe.2.1, StatefulScalarValues.cons firstSafe.2.2.represented tailSafe.2.2⟩

#print axioms evalArguments_statefulScalarList_world
end Goose.Proofs.ConstructionAcceptedExecution
