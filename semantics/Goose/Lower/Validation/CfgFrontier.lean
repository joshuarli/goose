import Goose.Lower.Frag

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LiveBound (state : LS) : Prop :=
  ∀ block, state.cur = some block → block < state.blocks.size

theorem liveBound_of_adv {before after : LS} (advance : before.Adv after)
    (bounded : LiveBound before) : LiveBound after := by
  intro block current
  rcases advance.cur with stopped | same | ⟨fresh, currentFresh, _, bound⟩
  · rw [stopped] at current
    cases current
  · exact Nat.lt_of_lt_of_le (bounded block (same.symm.trans current)) advance.ext.1
  · have equal : fresh = block := Option.some.inj (currentFresh.symm.trans current)
    exact equal ▸ bound

theorem liveBound_of_advB {action : B α} (advance : AdvB action) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (action env state).2 :=
  liveBound_of_adv (advance env state _ _ rfl) bounded

theorem liveBound_initState : LiveBound initState := by
  intro block current
  cases current

theorem liveBound_setCur {state : LS} {block : BlockId} (bound : block < state.blocks.size)
    (env : LEnv) : LiveBound (setCur (some block) env state).2 := by
  rw [setCur_run]
  intro current equal
  exact Option.some.inj equal ▸ bound

theorem liveBound_setCur_none (state : LS) (env : LEnv) :
    LiveBound (setCur none env state).2 := by
  rw [setCur_run]
  intro current equal
  cases equal

theorem liveBound_lowerExpr (expr : Expr) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (lowerExpr expr env state).2 :=
  liveBound_of_advB (advB_lowerExpr expr) env state bounded

theorem liveBound_lowerPlace (place : Place) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (lowerPlace place env state).2 :=
  liveBound_of_advB (advB_lowerPlace place) env state bounded

theorem liveBound_lowerView (view : View) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (lowerView view env state).2 :=
  liveBound_of_advB (advB_lowerView view) env state bounded

theorem liveBound_lowerBlock (context : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    (env : LEnv) (state : LS) (bounded : LiveBound state) :
    LiveBound (lowerBlock context pre want block env state).2 :=
  liveBound_of_advB (advB_lowerBlock context pre want block) env state bounded

theorem liveBound_lowerStmt (context : Option LoopCtx) (stmt : Stmt) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (lowerStmt context stmt env state).2 :=
  liveBound_of_advB (advB_lowerStmt context stmt) env state bounded

theorem liveBound_lowerStmts (context : Option LoopCtx) (stmts : List Stmt) (env : LEnv) (state : LS)
    (bounded : LiveBound state) : LiveBound (lowerStmts context stmts env state).2 :=
  liveBound_of_advB (advB_lowerStmts context stmts) env state bounded

def BoundedRun (invariant : LS → Prop) (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    invariant before → LiveBound before → invariant after

theorem BoundedRun.pure (invariant : LS → Prop) (value : α) :
    BoundedRun invariant (pure value) := by
  intro env before result after run holds _
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact holds

theorem BoundedRun.bind {invariant : LS → Prop} {first : B α} {next : α → B β}
    (advance : AdvB first) (one : BoundedRun invariant first)
    (two : ∀ result, BoundedRun invariant (next result)) :
    BoundedRun invariant (first >>= next) := by
  intro env before result after run holds bounded
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact two value env middle result after nextRun
    (one env before value middle firstRun holds bounded)
    (liveBound_of_adv (advance env before value middle firstRun) bounded)

theorem liveBound_newBlock (types : List VTy) (env : LEnv) (state : LS) :
    let (pair, after) := newBlock types env state
    pair.1 < after.blocks.size := by
  change state.blocks.size < (state.blocks.push _).size
  simp

theorem liveBound_fork {state : LS} {block : BlockId} (current : state.cur = some block)
    (condition : ValueId) (env : LEnv) :
    let (pair, after) := fork condition env state
    pair.1 < after.blocks.size ∧ pair.2 < after.blocks.size := by
  rw [fork_run condition env current]
  simp; nat_omega

theorem liveBound_scFork {state : LS} {block : BlockId} (current : state.cur = some block)
    (isAnd : Bool) (value : ValueId) (env : LEnv) :
    let (pair, after) := scFork isAnd value env state
    pair.1 < after.blocks.size ∧ pair.2.1 < after.blocks.size := by
  rw [scFork_run isAnd value env current]
  simp; nat_omega

end Goose.Lower.Validation
