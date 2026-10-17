import Goose.Lower.ReflectionSteps

namespace Goose.Lower.ReflectionChecks

open Goose.Core Goose.GIR

def infiniteSource : Core.Module :=
  { files := #["reflection.goose"], types := #[], globals := #[],
    impls := #[⟨"main",#[],#[],#[],
      .mk 0 [.while (.bool true) (.mk 1 [] none) 0] none,.unknown⟩],
    contexts := #[⟨0,"main",[],[],[]⟩], entry := 0, origins := #[⟨0,1,"while"⟩] }

def loopFunction : Func :=
  { name := "main", params := [], results := [], slots := #[], scopes := #[none,some 0],
    blocks := #[
      ⟨[],[.eff (.enter 0),.term (.br 1 [])]⟩,
      ⟨[],[.def 0 (.constBool true),.term (.condbr 0 2 [] 3 [])]⟩,
      ⟨[],[.eff (.enter 1),.eff (.leave 1),.term (.br 1 [])]⟩,
      ⟨[],[.eff (.leave 0),.term (.ret [] none)]⟩],
    summary := .unknown, org := none }

def loopContext : FnCtx := ⟨⟨.release,lower infiniteSource⟩,loopFunction⟩

theorem actual_lowered_loop : (lower infiniteSource).funcs[0]? = some loopFunction := by
  cbv

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem infiniteSource_accepted : Core.validate infiniteSource = .ok () := by cbv

theorem header_cycle (fuel : Nat) (frame : GIR.Frame) (state : St) :
    runAt loopContext (1,0) frame (fuel + 5) state =
      runAt loopContext (1,0) (frame.set 0 (.val (.bool true))) fuel
        { state with nextScope := state.nextScope + 1 } := by
  simp [runAt, loopContext, loopFunction, instsAt, exec, execOp, execPure,
    execEff, enterBlock, bindParams, mapList, getVal, getCell, setCell_eq,
    Frame.set, freshScope, releaseSlots, bind_apply, pure_apply]
  rfl

theorem header_timeout (fuel : Nat) (frame : GIR.Frame) (state : St) :
    ∃ after, runAt loopContext (1,0) frame fuel state = .stop .timeout after := by
  induction fuel using Nat.strongRecOn generalizing frame state with
  | ind fuel ih =>
      by_cases hsmall : fuel < 5
      · have bounded : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 := by omega
        rcases bounded with rfl | rfl | rfl | rfl | rfl <;>
          simp [runAt, loopContext, loopFunction, instsAt, exec, execOp, execPure,
            execEff, enterBlock, bindParams, mapList, getVal, getCell, setCell_eq,
            Frame.set, freshScope, GIR.releaseScope, releaseSlots, Core.expectBool,
            bind_apply, pure_apply, timeout, M.stop] <;> exact ⟨_,rfl⟩
      · obtain ⟨rest,rfl⟩ : ∃ rest, fuel = rest + 5 := ⟨fuel - 5,by omega⟩
        rw [header_cycle]
        exact ih rest (by omega) _ _

theorem entry_timeout (fuel : Nat) (frame : GIR.Frame) (state : St) :
    ∃ after, runAt loopContext (0,0) frame fuel state = .stop .timeout after := by
  cases fuel with
  | zero => exact ⟨state,rfl⟩
  | succ fuel =>
      cases fuel with
      | zero =>
          exact ⟨{state with nextScope := state.nextScope + 1},rfl⟩
      | succ fuel =>
          obtain ⟨after, result⟩ := header_timeout fuel
            { frame with scopes := (0,state.nextScope) :: frame.scopes }
            { state with nextScope := state.nextScope + 1 }
          exact ⟨after, result⟩

theorem divergent_target_reflection (source : Nat → M Val) (frame : GIR.Frame) (state : St) :
    ReflectM source (fun n => runAt loopContext (0,0) frame n) state := by
  intro fuel result hresult hrun
  obtain ⟨after,htimeout⟩ := entry_timeout fuel frame state
  exact (hresult after (hrun.symm.trans htimeout)).elim

theorem lowered_module_timeout (fuel : Nat) (state : St) :
    ∃ after, GIR.runModule fuel ⟨.release,lower infiniteSource⟩ state = .stop .timeout after := by
  have functions : (lower infiniteSource).funcs = #[loopFunction] := by cbv
  have globals : (lower infiniteSource).globals = #[] := by cbv
  have entry : (lower infiniteSource).entry = 0 := rfl
  simp only [GIR.runModule, globals, Array.size_empty, List.range_zero, GIR.initGlobals, pure_bind, entry]
  cases fuel with
  | zero => exact ⟨state,rfl⟩
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [callFn, lookupFn, functions, enterFn, timeout, M.stop, bind_apply, maxCallDepth]
      | succ fuel =>
          obtain ⟨after, result⟩ := entry_timeout fuel ⟨state.nextAct,[],{},1⟩
            { state with nextAct := state.nextAct + 1 }
          refine ⟨after, ?_⟩
          simp [runAt, loopContext, loopFunction, instsAt] at result
          simp [callFn, lookupFn, functions, enterFn, enterBlock, bindParams, mapList,
            freshAct, bind_apply, pure_apply, maxCallDepth, loopFunction, result]

theorem lowered_module_reflection :
    ReflectM (fun n => Core.runModule n ⟨.release,infiniteSource⟩)
      (fun n => GIR.runModule n ⟨.release,lower infiniteSource⟩) St.initial := by
  intro fuel result hresult hrun
  obtain ⟨after,htimeout⟩ := lowered_module_timeout fuel St.initial
  exact (hresult after (hrun.symm.trans htimeout)).elim

theorem lowered_infinite_never_faults (fuel : Nat) (kind : FaultKind) :
    GIR.run fuel .release (lower infiniteSource) ≠ .fault kind :=
  reflected_lowering_never_faults infiniteSource_accepted .release lowered_module_reflection fuel kind

end Goose.Lower.ReflectionChecks
