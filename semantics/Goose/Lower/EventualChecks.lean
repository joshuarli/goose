import Goose.Lower.Eventual
import Goose.GIR.Validate

namespace Goose.Lower.EventualChecks

open Goose.Core Goose.GIR

def callee : Func :=
  { name := "callee", params := [], results := [.int .i64], slots := #[], scopes := #[],
    blocks := #[⟨[], [.eff (.print [.text "callee"] (some 0)), .def 0 (.constInt .i64 42),
      .term (.ret [0] none)]⟩], summary := .unknown, org := none }

def caller : Func :=
  { name := "caller", params := [], results := [.int .i64], slots := #[], scopes := #[],
    blocks := #[⟨[], [.def 0 (.call 0 [] (some 0)), .eff (.print [.text "tail"] (some 0)),
      .term (.ret [0] none)]⟩], summary := .unknown, org := none }

def main : Func :=
  { name := "main", params := [], results := [], slots := #[], scopes := #[],
    blocks := #[⟨[], [.def 0 (.call 1 [] (some 0)), .term (.ret [] none)]⟩],
    summary := .unknown, org := none }

def target : GIR.Module :=
  { files := #["eventual.gir"], globals := #[], funcs := #[callee, caller, main], entry := 2,
    origins := #[⟨0, 1, "call"⟩] }

#guard match GIR.validate target with
  | .ok _ => true
  | .error _ => false

def context : FnCtx := ⟨⟨.release, target⟩, caller⟩

def frame : Frame := ⟨0, [], {}, 0⟩

def sourceCall : M Val := do
  let _ ← freshAct
  emit "callee\n"
  pure (.int .i64 42)

def sourceSequence : M Val := do
  let value ← sourceCall
  emit "tail\n"
  pure value

theorem actual_callee (k : Nat) : callFn (k + 5) context.cfg frame.depth 0 [] = sourceCall := by
  funext s
  simp [context, target, frame, callee, callFn, lookupFn, enterFn, enterBlock, bindParams,
    exec, execEff, execOp, execPure, renderPart, mapList, getVal, getCell, setCell,
    freshAct, emit, bind_apply, pure_apply, maxCallDepth]
  rfl

theorem callee_agrees (s : St) :
    EventualM sourceCall (fun k => callFn k context.cfg frame.depth 0 []) s := by
  refine ⟨fun a s1 hc => ⟨5, fun k hk => ?_⟩, fun e s1 hc _ => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simpa only [actual_callee] using hc
  · have hr : sourceCall s = .ok (.int .i64 42)
        { s with trace := s.trace ++ "callee\n", nextAct := s.nextAct + 1 } := rfl
    rw [hr] at hc
    cases hc

theorem call_simulation : SimE context (0, 0) frame sourceCall
    (fun value pt' fr' => pt' = (0, 1) ∧ fr' = frame.set 0 (.val value)) := by
  exact SimE.call_step rfl rfl callee_agrees

theorem sequence_simulation : SimE context (0, 0) frame sourceSequence
    (fun value pt' fr' => pt' = (0, 2) ∧ fr' = frame.set 0 (.val value)) := by
  apply SimE.bind call_simulation
  intro value pt' fr' hp
  obtain ⟨rfl, rfl⟩ := hp
  have he : SimE context (0, 1) (frame.set 0 (.val value)) (emit "tail\n")
      (fun _ pt' fr' => pt' = (0, 2) ∧ fr' = frame.set 0 (.val value)) := by
    apply SimE.eff_step (fun _ => frame.set 0 (.val value)) rfl
    simp [execEff, renderPart, mapList]
  exact SimE.bind he (fun _ _ _ hp => SimE.ret hp)

theorem sequence_agrees (s : St) :
    EventualM sourceSequence (fun k => runAt context (0, 0) frame k) s := by
  apply SimE.complete_ret1 sequence_simulation (r := 0) (org := none)
  intro value pt' fr' hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨rfl, Frame.set_get frame 0 (.val value)⟩

#guard match runAt context (0, 0) frame 7 St.initial with
  | .ok (Val.int IntTy.i64 42) s => s.trace == "callee\ntail\n" && s.nextAct == 1
  | _ => false

#guard match runAt context (0, 0) frame 6 St.initial with
  | .stop .timeout s => s.trace == "callee\n" && s.nextAct == 1
  | _ => false

#guard match runAt context (0, 1) (frame.set 0 (.val (.int .i64 42))) 1
    { St.initial with trace := "callee\n", nextAct := 1 } with
  | .stop .timeout s => s.trace == "callee\ntail\n" && s.nextAct == 1
  | _ => false

def afterCall : St := { St.initial with trace := "callee\n", nextAct := 1 }

def completionObservation : Res Val → Bool × String × Nat
  | .ok _ s => (true, s.trace, s.nextAct)
  | .stop _ s => (false, s.trace, s.nextAct)

theorem completed_at_seven : runAt context (0, 0) frame 7 St.initial =
    .ok (.int .i64 42) { St.initial with trace := "callee\ntail\n", nextAct := 1 } := by
  simp [runAt, instsAt, context, caller, target, callee, frame, exec, execOp, execPure,
    callFn, lookupFn, enterFn, enterBlock, bindParams, execEff, renderPart, mapList,
    getVal, getCell, setCell, Frame.set, Std.HashMap.getElem?_insert, freshAct, emit,
    bind_apply, pure_apply, maxCallDepth, St.initial]
  rfl

theorem no_exact_additive_call_prefix :
    ¬ ∃ d, ∀ j, runAt context (0, 0) frame (j + d) St.initial =
      runAt context (0, 1) (frame.set 0 (.val (.int .i64 42))) j afterCall := by
  intro ⟨d, hd⟩
  by_cases hlarge : 7 ≤ d
  · have hm := runAt_fuel_mono hlarge context (0, 0) frame St.initial
      (NonTimeout.ok (.int .i64 42) _) completed_at_seven
    have hzero := hd 0
    rw [Nat.zero_add, hm] at hzero
    change Res.ok _ _ = Res.stop .timeout _ at hzero
    cases hzero
  · have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      have hobs := congrArg completionObservation (hd 1)
      first
      | revert hobs; decide
      | rw [show 1 + 6 = 7 from rfl, completed_at_seven] at hobs
        revert hobs
        decide

def abortingCallee : Func :=
  { callee with blocks := #[⟨[], [.eff (.print [.text "callee"] (some 0)),
      .term (.abort .assert (some 0))]⟩] }

def abortingTarget : GIR.Module := { target with funcs := #[abortingCallee, caller, main] }

def abortingContext : FnCtx := ⟨⟨.release, abortingTarget⟩, caller⟩

def sourceAbort : M Val := do
  let _ ← freshAct
  emit "callee\n"
  abortAt .assert 0

theorem actual_aborting_callee (k : Nat) :
    callFn (k + 4) abortingContext.cfg frame.depth 0 [] = sourceAbort := by
  funext s
  simp [abortingContext, abortingTarget, target, frame, abortingCallee, callee, callFn,
    lookupFn, enterFn, enterBlock, bindParams, exec, execEff, renderPart, mapList,
    freshAct, emit, abortAtOrg, abortAt, M.stop, bind_apply, pure_apply, maxCallDepth]
  rfl

theorem aborting_callee_agrees (s : St) :
    EventualM sourceAbort (fun k => callFn k abortingContext.cfg frame.depth 0 []) s := by
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ⟨4, fun k hk => ?_⟩⟩
  · have hr : sourceAbort s = .stop (.abort .assert 0)
        { s with trace := s.trace ++ "callee\n", nextAct := s.nextAct + 1 } := rfl
    rw [hr] at hc
    cases hc
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    simpa only [actual_aborting_callee] using hc

theorem aborting_call_simulation : SimE abortingContext (0, 0) frame sourceAbort
    (fun value pt' fr' => pt' = (0, 1) ∧ fr' = frame.set 0 (.val value)) :=
  SimE.call_step rfl rfl aborting_callee_agrees

#guard match GIR.validate abortingTarget with
  | .ok _ => true
  | .error _ => false

#guard match runAt abortingContext (0, 0) frame 6 St.initial with
  | .stop (.abort AbortKind.assert 0) s => s.trace == "callee\n" && s.nextAct == 1
  | _ => false

end Goose.Lower.EventualChecks
