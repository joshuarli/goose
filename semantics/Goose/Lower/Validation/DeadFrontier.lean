import Goose.Lower.Validation.ScalarTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def DeadRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) → before.cur = none → after.cur = none

theorem DeadRun.pure (value : α) : DeadRun (pure value) := by
  intro le before result after run dead
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact dead

theorem DeadRun.bind {action : B α} {next : α → B β}
    (first : DeadRun action) (second : ∀ value, DeadRun (next value)) :
    DeadRun (action >>= next) := by
  intro le before result after run dead
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ _ secondRun (first _ _ _ _ firstRun dead)

theorem DeadRun.of_cur_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.cur = state.cur) : DeadRun action := by
  intro le before result after run dead
  have same := unchanged le before
  rw [run] at same
  exact same.trans dead

theorem dead_emitDef (op : Op) : DeadRun (emitDef op) := by
  intro le before result after run dead
  rw [emitDef_none op le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact dead

theorem dead_emitEffect (effect : Effect) : DeadRun (emitEffect effect) := by
  intro le before result after run dead
  rw [emitEffect_none effect le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact dead

theorem dead_emitTerm (term : Term) : DeadRun (emitTerm term) := by
  intro le before result after run dead
  rw [emitTerm_none term le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact dead

theorem dead_whenLive (default : α) (action : BlockId → B α) : DeadRun (whenLive default action) := by
  intro le before result after run dead
  rw [whenLive_none default action le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact dead

theorem dead_read : DeadRun (read : B LEnv) := by
  apply DeadRun.of_cur_unchanged
  intros
  rfl

theorem dead_valTy (value : ValueId) : DeadRun (valTy value) := by
  apply DeadRun.of_cur_unchanged
  intro le state
  rw [valTy_run]

theorem dead_intTyOf (value : ValueId) : DeadRun (intTyOf value) := by
  unfold intTyOf
  refine DeadRun.bind (dead_valTy value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact DeadRun.pure _
  | view _ _ => exact DeadRun.pure _

theorem dead_freezeTo (mu : Mutability) (value : ValueId) : DeadRun (freezeTo mu value) := by
  unfold freezeTo
  refine DeadRun.bind (dead_valTy value) fun ty => ?_
  cases mu <;> cases ty <;> first
    | exact DeadRun.pure _
    | (rename_i ty; cases ty <;> first
      | exact DeadRun.pure _
      | (rename_i mu ty; cases mu <;> first | exact DeadRun.pure _ | exact dead_emitDef _))

theorem dead_shortCircuit (isAnd : Bool) (value : ValueId) (rhs : B ValueId) :
    DeadRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact dead_whenLive _ _

theorem dead_pushScope (scope : ScopeId) : DeadRun (pushScope scope) := by
  apply DeadRun.of_cur_unchanged
  intro le state
  rw [pushScope_run]

theorem dead_popScope : DeadRun popScope := by
  apply DeadRun.of_cur_unchanged
  intro le state
  rw [popScope_run]

theorem dead_inScope (scope : ScopeId) {action : B α} (dead : DeadRun action) : DeadRun (inScope scope action) := by
  unfold inScope
  exact DeadRun.bind (dead_pushScope _) fun _ =>
    DeadRun.bind dead fun _ => DeadRun.bind dead_popScope fun _ => DeadRun.pure _

theorem dead_initSlots : ∀ pre, DeadRun (initSlots pre)
  | [] => DeadRun.pure _
  | (_, _, _) :: rest => DeadRun.bind (dead_emitEffect _) fun _ => dead_initSlots rest

theorem dead_lowerStmts (context : Option LoopCtx) (stmts : List Stmt) : DeadRun (lowerStmts context stmts) := by
  intro le before result after run dead
  cases stmts with
  | nil =>
    rw [lowerStmts, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact dead
  | cons stmt rest =>
    simp only [lowerStmts, bind_run, isLive_none dead, Bool.false_eq_true, ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact dead

mutual

theorem dead_lowerExpr : ∀ e : Expr, DeadRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExprs es) fun _ => dead_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact dead_emitDef _
  | .bool b => by simp only [lowerExpr]; exact dead_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerPlace p) fun _ => dead_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerPlace p) fun r => dead_freezeTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerView v) fun _ => DeadRun.bind (dead_lowerBound lo) fun _ =>
      DeadRun.bind (dead_lowerBound hi) fun _ => dead_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerView v) fun _ => dead_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr e) fun a => DeadRun.bind (dead_intTyOf a) fun _ => dead_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr a) fun x => DeadRun.bind (dead_lowerExpr b) fun y =>
      DeadRun.bind (dead_intTyOf x) fun _ => dead_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine DeadRun.bind (dead_lowerExpr a) fun x => DeadRun.bind (dead_lowerExpr b) fun y =>
      DeadRun.bind (dead_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact dead_emitDef _
    | view _ _ => exact dead_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr a) fun x => dead_shortCircuit true x (lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr a) fun x => dead_shortCircuit false x (lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => dead_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr e) fun a => DeadRun.bind (dead_intTyOf a) fun _ => dead_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerArgs args) fun _ =>
      DeadRun.bind (dead_emitDef _) fun r => DeadRun.bind dead_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact DeadRun.pure _ | exact DeadRun.bind (dead_emitTerm _) fun _ => DeadRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerPlace owner) fun r => DeadRun.bind (dead_lowerExpr e) fun v =>
      dead_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerPlace owner) fun _ => dead_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr c) fun cv =>
      dead_whenLive _ _
  | .blockE b => by
    simp only [lowerExpr]
    exact dead_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExprs es) fun _ => dead_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => dead_emitDef _

theorem dead_lowerExprs : ∀ es : List Expr, DeadRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact DeadRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => DeadRun.bind (dead_lowerExprs rest) fun _ => DeadRun.pure _

theorem dead_lowerArg : ∀ a : Arg, DeadRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact dead_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact DeadRun.bind (dead_lowerPlace p) fun r => dead_freezeTo m r

theorem dead_lowerArgs : ∀ as : List Arg, DeadRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact DeadRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact DeadRun.bind (dead_lowerArg a) fun _ => DeadRun.bind (dead_lowerArgs rest) fun _ => DeadRun.pure _

theorem dead_lowerPlace : ∀ p : Place, DeadRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact DeadRun.bind (dead_lowerPlace owner) fun _ => dead_emitDef _
  | .var x => by simp only [lowerPlace]; exact dead_emitDef _
  | .global g => by simp only [lowerPlace]; exact dead_emitDef _
  | .deref e => by simp only [lowerPlace]; exact dead_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact DeadRun.bind (dead_lowerView v) fun _ => DeadRun.bind (dead_lowerExpr i) fun _ => dead_emitDef _

theorem dead_lowerView : ∀ v : View, DeadRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact DeadRun.bind (dead_lowerPlace p) fun _ => dead_emitDef _
  | .val e => by
    simp only [lowerView]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => dead_emitDef _

theorem dead_lowerBound : ∀ b : Bound, DeadRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact DeadRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => DeadRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => DeadRun.pure _

theorem dead_lowerEachSource : ∀ v : View, DeadRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact DeadRun.bind (dead_lowerPlace p) fun _ => DeadRun.bind (dead_emitDef _) fun _ => DeadRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact DeadRun.bind (dead_lowerExpr e) fun _ => DeadRun.bind (dead_emitDef _) fun _ => DeadRun.pure _

theorem dead_lowerBlockValue (want : Bool) : ∀ v : Option Expr, DeadRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact dead_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact DeadRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact dead_emitDef _

theorem dead_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, DeadRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact DeadRun.bind (dead_emitEffect _) fun _ => dead_inScope sc
      (DeadRun.bind (dead_initSlots _) fun _ => DeadRun.bind (dead_lowerStmts lc stmts) fun _ =>
        DeadRun.bind (dead_lowerBlockValue want value) fun _ => DeadRun.bind (dead_emitEffect _) fun _ =>
        DeadRun.pure _)

end

theorem DeadRun.live_before {action : B α} (dead : DeadRun action)
    {le : LEnv} {before after : LS} {result : α} (run : action le before = (result, after))
    (live : after.cur.isSome = true) : before.cur.isSome = true := by
  cases current : before.cur with
  | none =>
    have stopped := dead le before result after run current
    simp [stopped] at live
  | some block => simp

end Goose.Lower.Validation
