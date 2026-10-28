import Goose.Proofs.Fuel
import Goose.GIR.Lemmas

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

inductive CallArgumentsDone (cfg : Cfg) (env : Env) : List Arg → St → List Val → St → Prop
  | nil (state : St) : CallArgumentsDone cfg env [] state [] state
  | cons {argument : Arg} {rest : List Arg} {state middle after : St} {value : Val} {values : List Val} {fuel : Nat}
      (evaluated : evalArg fuel cfg env argument state = .ok value middle)
      (tail : CallArgumentsDone cfg env rest middle values after) :
      CallArgumentsDone cfg env (argument :: rest) state (value :: values) after

theorem CallArgumentsDone.fuel {cfg : Cfg} {env : Env} {arguments : List Arg} {state after : St}
    {values : List Val} (trace : CallArgumentsDone cfg env arguments state values after) :
    ∃ fuel, mapList (evalArg fuel cfg env) arguments state = .ok values after := by
  induction trace with
  | nil state => exact ⟨0, by simp [mapList, pure_apply]⟩
  | @cons argument rest state middle after value values fuel evaluated tail ih =>
    obtain ⟨tailFuel, tailDone⟩ := ih
    let joined := max fuel tailFuel
    have headDone := ((monoAll fuel joined (Nat.le_max_left _ _)).arg cfg env argument state).1 value middle evaluated
    have later := (MonoM.mapList (fun arg => (monoAll tailFuel joined (Nat.le_max_right _ _)).arg cfg env arg) rest middle).1 values after tailDone
    exact ⟨joined, by simp only [mapList, bind_apply, headDone, later, pure_apply]⟩

inductive CallArgumentsStopped (cfg : Cfg) (env : Env) : List Arg → St → Stop → St → Prop
  | head {argument : Arg} {rest : List Arg} {state after : St} {fuel : Nat} {stop : Stop}
      (evaluated : evalArg fuel cfg env argument state = .stop stop after) (nonTimeout : stop ≠ .timeout) :
      CallArgumentsStopped cfg env (argument :: rest) state stop after
  | tail {argument : Arg} {rest : List Arg} {state middle after : St} {value : Val} {fuel : Nat} {stop : Stop}
      (evaluated : evalArg fuel cfg env argument state = .ok value middle)
      (tail : CallArgumentsStopped cfg env rest middle stop after) :
      CallArgumentsStopped cfg env (argument :: rest) state stop after

theorem CallArgumentsStopped.fuel {cfg : Cfg} {env : Env} {arguments : List Arg} {state after : St}
    {stop : Stop} (trace : CallArgumentsStopped cfg env arguments state stop after) :
    stop ≠ .timeout ∧ ∃ fuel, mapList (evalArg fuel cfg env) arguments state = .stop stop after := by
  induction trace with
  | @head argument rest state after fuel stop evaluated nonTimeout => exact ⟨nonTimeout, fuel, by simp [mapList, bind_apply, evaluated]⟩
  | @tail argument rest state middle after value fuel stop evaluated tail ih =>
    obtain ⟨nonTimeout, tailFuel, tailDone⟩ := ih
    let joined := max fuel tailFuel
    have headDone := ((monoAll fuel joined (Nat.le_max_left _ _)).arg cfg env argument state).1 value middle evaluated
    have later := (MonoM.mapList (fun arg => (monoAll tailFuel joined (Nat.le_max_right _ _)).arg cfg env arg) rest middle).2 stop after tailDone
    rcases later with timeout | later
    · cases stop <;> simp [isTimeout] at timeout nonTimeout
    · exact ⟨nonTimeout, joined, by simp only [mapList, bind_apply, headDone, later]⟩

theorem CallArgumentsDone.appendStopped {cfg : Cfg} {env : Env} {arguments : List Arg} {state middle : St}
    {values : List Val} (trace : CallArgumentsDone cfg env arguments state values middle)
    {rest : List Arg} {stop : Stop} {after : St} (tail : CallArgumentsStopped cfg env rest middle stop after) :
    CallArgumentsStopped cfg env (arguments ++ rest) state stop after := by
  induction trace with
  | nil => exact tail
  | cons evaluated prior ih => exact .tail evaluated (ih tail)

theorem CallArgumentsDone.byValStop {cfg : Cfg} {env : Env} {arguments : List Arg} {state middle : St}
    {values : List Val} (trace : CallArgumentsDone cfg env arguments state values middle)
    {expression : Expr} {rest : List Arg} {fuel : Nat} {stop : Stop} {after : St}
    (evaluated : evalExpr fuel cfg env expression middle = .stop stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ joined, mapList (evalArg joined cfg env) (arguments ++ .byVal expression :: rest) state = .stop stop after := by
  have head : CallArgumentsStopped cfg env (.byVal expression :: rest) middle stop after :=
    .head (fuel := fuel + 1) (by simpa [evalArg] using evaluated) nonTimeout
  exact (trace.appendStopped head).fuel.2

#print axioms CallArgumentsDone.fuel
#print axioms CallArgumentsStopped.fuel
#print axioms CallArgumentsDone.byValStop
end Goose.Lower
