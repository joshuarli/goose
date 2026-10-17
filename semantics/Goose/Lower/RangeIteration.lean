import Goose.Lower.Loops
import Goose.Lower.FlowState
import Goose.Lower.RuntimeSim

namespace Goose.Lower

open Goose.Core Goose.GIR

def preparedRange (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (ty : IntTy)
    (current upper : Int) (body : Core.Block) : M Flow :=
  if current < upper then
    (execBlock n cfg env [(x, .int ty current)] body >>= prepareReturn env) >>= fun flow =>
      match flow with
      | .normal _ | .cont => execRange n cfg env x ty (current + 1) upper body >>= prepareReturn env
      | .brk => pure (.normal .unit)
      | .ret value => pure (.ret value)
  else pure (.normal .unit)

theorem prepareReturn_execRange (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (ty : IntTy)
    (current upper : Int) (body : Core.Block) :
    (execRange (n + 1) cfg env x ty current upper body >>= prepareReturn env) =
      preparedRange n cfg env x ty current upper body := by
  conv => lhs; unfold execRange
  by_cases inside : current < upper
  · simp only [preparedRange, inside, ite_true, bind_assoc]
    congr 1
    funext flow
    cases flow <;> simp [prepareReturn, bind_assoc, pure_bind]
  · simp [preparedRange, inside, prepareReturn]

def RangeStepPost (cx : FnCtx) (header : Pt) (invariant : Int → Frame → Prop)
    (post : Flow → Pt → Frame → Prop) (current : Int) (flow : Flow) (point : Pt) (frame : Frame) : Prop :=
  match flow with
  | .normal _ | .cont => ∃ next, invariant (current + 1) next ∧ Goes cx point frame header next
  | .brk => post (.normal .unit) point frame
  | .ret value => post (.ret value) point frame

theorem range_sim_at (n : Nat) (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (ty : IntTy)
    (upper : Int) (block : Core.Block) (header body : Pt)
    (headerInv bodyInv : Int → Frame → Prop) (allowed : Int → St → Prop)
    (post : Flow → Pt → Frame → Prop)
    (branch : RangeBranch cx header body upper headerInv bodyInv post)
    (bodySimulation : ∀ fuel, fuel < n → ∀ current frame state,
      bodyInv current frame → allowed current state →
      SimEAt cx body frame (execBlock fuel cfg env [(x, .int ty current)] block >>= prepareReturn env)
        (RangeStepPost cx header headerInv post current) state)
    (retained : ∀ fuel, fuel < n → ∀ current state flow after, allowed current state →
      (execBlock fuel cfg env [(x, .int ty current)] block >>= prepareReturn env) state = .ok flow after →
      (match flow with | .normal _ | .cont => allowed (current + 1) after | _ => True)) :
    ∀ current frame state, headerInv current frame → allowed current state →
      SimEAt cx header frame (execRange n cfg env x ty current upper block >>= prepareReturn env) post state := by
  induction n with
  | zero =>
    intro current frame state invariant source
    simp only [execRange]
    exact SimEAt.of_simG SimG.of_timeout_bind state
  | succ n induction =>
    intro current frame state invariant source
    rw [prepareReturn_execRange]
    unfold preparedRange
    have decision := branch current frame invariant
    by_cases inside : current < upper
    · simp only [inside, ite_true] at decision ⊢
      obtain ⟨entered, bodyInvariant, enter⟩ := decision
      apply SimEAt.goes enter
      refine SimEAt.bind (bodySimulation n (Nat.lt_succ_self n) current entered state bodyInvariant source)
        fun flow after point final done result => ?_
      cases flow with
      | normal value | cont =>
        obtain ⟨next, nextInvariant, reenter⟩ := result
        have sourceNext := retained n (Nat.lt_succ_self n) current state _ after source done
        exact SimEAt.goes reenter (induction
          (fun fuel bound => bodySimulation fuel (Nat.lt_trans bound (Nat.lt_succ_self n)))
          (fun fuel bound => retained fuel (Nat.lt_trans bound (Nat.lt_succ_self n)))
          (current + 1) next after nextInvariant sourceNext)
      | brk => exact SimEAt.ret result
      | ret value => exact SimEAt.ret result
    · simp only [inside, ite_false] at decision ⊢
      obtain ⟨point, final, result, exit⟩ := decision
      exact SimEAt.goes exit (SimEAt.ret result)

end Goose.Lower
