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

theorem scalar_read_argument_stop_fuel {cfg : Cfg} {env : Env} {place : Place} {state after : St} {stop : Stop}
    (form : ScalarReadPlace place) {fuel : Nat}
    (evaluated : evalArg fuel cfg env (.byVal (.read place)) state = .stop stop after)
    (nonTimeout : stop ≠ .timeout) :
    evalArg 3 cfg env (.byVal (.read place)) state = .stop stop after := by
  cases fuel with
  | zero => simp [evalArg, timeout, M.stop] at evaluated; exact (nonTimeout evaluated.1.symm).elim
  | succ fuel =>
    cases fuel with
    | zero => simp [evalArg, evalExpr, timeout, M.stop] at evaluated; exact (nonTimeout evaluated.1.symm).elim
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [evalArg, evalExpr, evalPlace, timeout, M.stop, bind_apply] at evaluated
        exact (nonTimeout evaluated.1.symm).elim
      | succ fuel =>
        cases form <;> simpa only [evalArg, evalExpr, evalPlace] using evaluated

#print axioms scalar_read_argument_stop_fuel

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

theorem evalArg_success_stop_disjoint {cfg : Cfg} {env : Env} {argument : Arg} {state firstState secondState : St}
    {value : Val} {stop : Stop} {firstFuel secondFuel : Nat}
    (success : evalArg firstFuel cfg env argument state = .ok value firstState)
    (stopped : evalArg secondFuel cfg env argument state = .stop stop secondState)
    (nonTimeout : stop ≠ .timeout) : False := by
  have firstPromoted := ((monoAll firstFuel (max firstFuel secondFuel) (Nat.le_max_left _ _)).arg cfg env argument state).1 value firstState success
  have secondPromoted := ((monoAll secondFuel (max firstFuel secondFuel) (Nat.le_max_right _ _)).arg cfg env argument state).2 stop secondState stopped
  rcases secondPromoted with timeout | promoted
  · cases stop <;> simp_all [isTimeout]
  · cases firstPromoted.symm.trans promoted

#print axioms evalArg_success_stop_disjoint

#print axioms evalArg_success_unique
end Goose.Lower
