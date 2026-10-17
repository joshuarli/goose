import Goose.Lower.ReflectionChecks

namespace Goose.Lower.ReflectionChecks

open Goose.Core Goose.GIR

theorem core_while_cycle (fuel : Nat) (cfg : Cfg) (env : Env) (state : St)
    (variables : env.vars = #[]) :
    Core.execWhile (fuel + 3) cfg env (.bool true) (.mk 1 [] none) state =
      Core.execWhile (fuel + 2) cfg env (.bool true) (.mk 1 [] none)
        { state with nextScope := state.nextScope + 1 } := by
  simp [Core.execWhile, Core.evalExpr, Core.expectBool, Core.execBlock, Core.execStmts,
    freshScope, bindAll, Core.releaseScope, Core.releaseVars, variables, bind_apply, pure_apply]

theorem core_while_timeout (fuel : Nat) (cfg : Cfg) (env : Env) (state : St)
    (variables : env.vars = #[]) :
    ∃ after, Core.execWhile fuel cfg env (.bool true) (.mk 1 [] none) state = .stop .timeout after := by
  induction fuel using Nat.strongRecOn generalizing state with
  | ind fuel ih =>
      by_cases small : fuel < 3
      · have bounded : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 := by omega
        rcases bounded with rfl | rfl | rfl <;>
          simp [Core.execWhile, Core.evalExpr, Core.expectBool, Core.execBlock, Core.execStmts,
            freshScope, bindAll, bind_apply, pure_apply, timeout, M.stop] <;> exact ⟨_,rfl⟩
      · obtain ⟨remaining,rfl⟩ : ∃ remaining, fuel = remaining + 3 := ⟨fuel - 3,by omega⟩
        rw [core_while_cycle _ _ _ _ variables]
        exact ih (remaining + 2) (by omega) _

theorem infinite_source_timeout (fuel : Nat) (state : St) :
    ∃ after, Core.runModule fuel ⟨.release,infiniteSource⟩ state = .stop .timeout after := by
  by_cases small : fuel < 4
  · have bounded : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 := by omega
    rcases bounded with rfl | rfl | rfl | rfl <;>
      simp [Core.runModule, Core.initGlobals, infiniteSource, Core.enterCall, lookupContext,
        lookupImpl, Core.execBlock, Core.execStmts, Core.execStmt, freshAct, freshScope,
        bindAll, bind_apply, pure_apply, timeout, M.stop, maxCallDepth] <;> exact ⟨_,rfl⟩
  · obtain ⟨remaining,rfl⟩ : ∃ remaining, fuel = remaining + 4 := ⟨fuel - 4,by omega⟩
    obtain ⟨after, result⟩ := core_while_timeout remaining ⟨.release,infiniteSource⟩
      ⟨#[],state.nextAct,[(0,state.nextScope)],1⟩
      { state with nextAct := state.nextAct + 1, nextScope := state.nextScope + 1 } rfl
    refine ⟨after, ?_⟩
    simp only [infiniteSource] at result
    simp [Core.runModule, Core.initGlobals, infiniteSource, Core.enterCall, lookupContext,
      lookupImpl, Core.execBlock, Core.execStmts, Core.execStmt, freshAct, freshScope,
      bindAll, bind_apply, pure_apply, maxCallDepth, result]

end Goose.Lower.ReflectionChecks
