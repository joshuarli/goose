import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower.DemandRuntimePrefixChecks

open Goose.Core Goose.GIR Goose.Evidence

private def callee : Func :=
  { name := "callee", params := [], results := [], slots := #[], scopes := #[],
    blocks := #[⟨[], [.term (.ret [] none)]⟩], summary := .unknown, org := none }

private def caller : Func :=
  { callee with name := "caller", blocks := #[⟨[], [.def 0 (.call 0 [] none)]⟩] }

private def config : GCfg :=
  ⟨.release, { files := #[], globals := #[], funcs := #[callee], entry := 0, origins := #[] }⟩

private def context : FnCtx := ⟨config, caller⟩
private def frame : Frame := ⟨0, [], {}, 1⟩
private def after : St := { St.initial with nextAct := 1 }

theorem call_zero_fuel_timeout : execOp 0 context frame (.call 0 [] none) St.initial =
    .stop .timeout St.initial := by simp only [execOp, timeout, M.stop]

theorem call_four_fuel_success : execOp 4 context frame (.call 0 [] none) St.initial =
    .ok (.val .unit) after := by
  simp [execOp, callFn, enterFn, exec, mapList, lookupFn, context, config, callee, frame,
    enterBlock, bindParams, bind_apply, pure_apply, maxCallDepth, after]
  rfl

theorem successful_call_step_uses_independent_fuel (extra : Nat) :
    DemandInstructionStep context (4 + extra)
      ⟨(0, 0), frame, St.initial⟩ ⟨(0, 1), frame.set 0 (.val .unit), after⟩ := by
  apply DemandInstructionStep.definition (by rfl)
  exact Goose.Proofs.GIRFuel.execOp_success_fuel_mono (by omega) call_four_fuel_success

theorem arbitrary_call_prefix_matches_smaller_fuel_traversal {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix context 1 ⟨(0, 0), frame, St.initial⟩ runtime) :
    runtime.state.nextAct ≤ 1 := by
  have traversal : DemandTraversal context (fun runtime => runtime.state.nextAct ≤ 1) 1 5
      ⟨(0, 0), frame, St.initial⟩ ⟨(0, 1), frame.set 0 (.val .unit), after⟩ :=
    .next (by decide) (successful_call_step_uses_independent_fuel 0) (.done 4 (by decide))
  exact traversal.runtimePrefix_invariant (by omega) steps

end Goose.Lower.DemandRuntimePrefixChecks
