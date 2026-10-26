import Goose.Proofs.ConstructionAcceptedElementWrite
import Goose.Proofs.ConstructionFixedBytes

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private theorem renew_open_destination (layout : LayoutEnv) (state : ExecutionState)
    (id : Nat) (ty : Ty) (count : Nat)
    (ready : OpenDestinationBacking layout state id ty count)
    (current : destinationCurrent state.construction id = .ok id) :
    renewReceivingDestination id state.construction = .ok id state.construction := by
  simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
    lookupDestination_result, ready.present, ready.opened]

theorem buildElement_fixed_open_backing (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (parent : Nat) (owner element : Ty)
    (operand : Expr) (count width : Nat) (before middle after : ExecutionState) (value : Value)
    (fixed : element.nonfixed = false)
    (sized : fixedByteSize? config.layout element = some width)
    (evaluated : evalValue fuel config environment operand before = .ok value middle)
    (ready : OpenDestinationBacking config.layout middle parent owner count)
    (elementType : ready.element = element)
    (current : destinationCurrent middle.construction parent = .ok parent)
    (executed : buildElement (fuel + 1) config environment parent element operand before = .ok () after) :
    Nonempty (OpenDestinationBacking config.layout after parent owner (count + 1)) := by
  have renewed := renew_open_destination config.layout middle parent owner count ready current
  simp only [buildElement, fixed, Bool.false_eq_true, ↓reduceIte, bind, evaluated] at executed
  cases encoded : fixedBytes fuel config.layout element value with
  | error reason => simp [encoded, Goose.Construct.liftExcept, EvalM.stop] at executed
  | ok payload =>
    simp only [encoded, Goose.Construct.liftExcept, pure] at executed
    have widthEqual := fixedBytes_size fuel config.layout element value payload width sized encoded
    have packed : packedEnd 1 config.layout ready.element payload 0 = .ok payload.size := by
      rw [elementType]
      simp only [packedEnd, sized, Nat.zero_add, widthEqual, gt_iff_lt,
        Nat.lt_irrefl, ↓reduceIte, pure, Except.pure]
    simp only [receivingAction, liftConstruction, bind, renewed] at executed
    cases written : writeElement parent payload middle.construction with
    | fault reason final => simp [written] at executed
    | ok result final =>
      cases result
      simp only [written, ExecutionStep.ok.injEq, true_and] at executed
      subst after
      exact writeElement_open_backing config.layout middle final parent owner count payload ready
        ⟨1, packed⟩ written

#print axioms buildElement_fixed_open_backing

end Goose.Proofs.ConstructionAcceptedExecution
