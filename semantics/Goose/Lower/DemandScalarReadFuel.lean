import Goose.Lower.DemandScalarReadForward

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem scalar_read_argument_success_fuel {cfg : Cfg} {env : Env} {place : Place} {state after : St} {value : Val}
    (form : ScalarReadPlace place) {fuel : Nat}
    (evaluated : evalArg fuel cfg env (.byVal (.read place)) state = .ok value after) :
    evalArg 3 cfg env (.byVal (.read place)) state = .ok value after := by
  cases fuel with
  | zero => simp [evalArg, timeout, M.stop] at evaluated
  | succ fuel =>
    cases fuel with
    | zero => simp [evalArg, evalExpr, timeout, M.stop] at evaluated
    | succ fuel =>
      cases fuel with
      | zero => simp [evalArg, evalExpr, evalPlace, timeout, M.stop, bind_apply] at evaluated
      | succ fuel =>
        cases form <;> simpa only [evalArg, evalExpr, evalPlace] using evaluated

#print axioms scalar_read_argument_success_fuel
end Goose.Lower

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem evalArg_success_unique {cfg : Cfg} {env : Env} {argument : Arg} {state firstState secondState : St}
    {first second : Val} {firstFuel secondFuel : Nat}
    (firstDone : evalArg firstFuel cfg env argument state = .ok first firstState)
    (secondDone : evalArg secondFuel cfg env argument state = .ok second secondState) :
    first = second ∧ firstState = secondState := by
  have firstPromoted := ((monoAll firstFuel (max firstFuel secondFuel) (Nat.le_max_left _ _)).arg cfg env argument state).1 first firstState firstDone
  have secondPromoted := ((monoAll secondFuel (max firstFuel secondFuel) (Nat.le_max_right _ _)).arg cfg env argument state).1 second secondState secondDone
  exact Res.ok.inj (firstPromoted.symm.trans secondPromoted)

#print axioms evalArg_success_unique
end Goose.Lower
