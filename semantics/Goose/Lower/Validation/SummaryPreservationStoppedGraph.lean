import Goose.Lower.Frag

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def StoppedGraph (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) → before.cur = none →
    after.cur = none ∧ after.blocks = before.blocks ∧ after.vals = before.vals

theorem StoppedGraph.pure (value : α) : StoppedGraph (pure value) := by
  intro le before result after run dead
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨dead, rfl, rfl⟩

theorem StoppedGraph.bind {action : B α} {next : α → B β}
    (first : StoppedGraph action) (second : ∀ value, StoppedGraph (next value)) :
    StoppedGraph (action >>= next) := by
  intro le before result after run dead
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  obtain ⟨midDead, midBlocks, midValues⟩ := first _ _ _ _ firstRun dead
  obtain ⟨afterDead, afterBlocks, afterValues⟩ := second value _ _ _ _ secondRun midDead
  exact ⟨afterDead, afterBlocks.trans midBlocks, afterValues.trans midValues⟩

theorem StoppedGraph.of_graph_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.cur = state.cur ∧
      (action le state).2.blocks = state.blocks ∧ (action le state).2.vals = state.vals) :
    StoppedGraph action := by
  intro le before result after run dead
  have same := unchanged le before
  rw [run] at same
  exact ⟨same.1.trans dead, same.2⟩

theorem stopped_emitDef (op : Op) : StoppedGraph (emitDef op) := by
  intro le before result after run dead
  rw [emitDef_none op le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨dead, rfl, rfl⟩

theorem stopped_emitEffect (effect : Effect) : StoppedGraph (emitEffect effect) := by
  intro le before result after run dead
  rw [emitEffect_none effect le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨dead, rfl, rfl⟩

theorem stopped_emitTerm (term : Term) : StoppedGraph (emitTerm term) := by
  intro le before result after run dead
  rw [emitTerm_none term le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨dead, rfl, rfl⟩

theorem stopped_whenLive (default : α) (action : BlockId → B α) : StoppedGraph (whenLive default action) := by
  intro le before result after run dead
  rw [whenLive_none default action le dead] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨dead, rfl, rfl⟩

theorem stopped_read : StoppedGraph (read : B LEnv) := by
  apply StoppedGraph.of_graph_unchanged
  intros
  exact ⟨rfl, rfl, rfl⟩

theorem stopped_valTy (value : ValueId) : StoppedGraph (valTy value) := by
  apply StoppedGraph.of_graph_unchanged
  intro le state
  rw [valTy_run]
  exact ⟨rfl, rfl, rfl⟩

theorem stopped_intTyOf (value : ValueId) : StoppedGraph (intTyOf value) := by
  unfold intTyOf
  refine StoppedGraph.bind (stopped_valTy value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> exact StoppedGraph.pure _
  | view _ _ => exact StoppedGraph.pure _

theorem stopped_freezeTo (mu : Mutability) (value : ValueId) : StoppedGraph (freezeTo mu value) := by
  unfold freezeTo
  refine StoppedGraph.bind (stopped_valTy value) fun ty => ?_
  cases mu <;> cases ty <;> first
    | exact StoppedGraph.pure _
    | (rename_i ty; cases ty <;> first
      | exact StoppedGraph.pure _
      | (rename_i mu ty; cases mu <;> first | exact StoppedGraph.pure _ | exact stopped_emitDef _))

theorem stopped_borrowTo (mu : Mutability) (value : ValueId) : StoppedGraph (borrowTo mu value) := by
  intro le before result after run
  rcases borrowTo_cases run with frozen | borrowed
  · exact stopped_freezeTo mu value le before result after frozen
  · exact stopped_emitDef _ le before result after borrowed

theorem stopped_shortCircuit (isAnd : Bool) (value : ValueId) (rhs : B ValueId) :
    StoppedGraph (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact stopped_whenLive _ _

theorem stopped_pushScope (scope : ScopeId) : StoppedGraph (pushScope scope) := by
  apply StoppedGraph.of_graph_unchanged
  intro le state
  rw [pushScope_run]
  exact ⟨rfl, rfl, rfl⟩

theorem stopped_popScope : StoppedGraph popScope := by
  apply StoppedGraph.of_graph_unchanged
  intro le state
  rw [popScope_run]
  exact ⟨rfl, rfl, rfl⟩

theorem stopped_inScope (scope : ScopeId) {action : B α} (dead : StoppedGraph action) : StoppedGraph (inScope scope action) := by
  unfold inScope
  exact StoppedGraph.bind (stopped_pushScope _) fun _ =>
    StoppedGraph.bind dead fun _ => StoppedGraph.bind stopped_popScope fun _ => StoppedGraph.pure _

theorem stopped_initSlots : ∀ pre, StoppedGraph (initSlots pre)
  | [] => StoppedGraph.pure _
  | (_, _, _) :: rest => StoppedGraph.bind (stopped_emitEffect _) fun _ => stopped_initSlots rest

theorem stopped_lowerStmts (context : Option LoopCtx) (stmts : List Stmt) : StoppedGraph (lowerStmts context stmts) := by
  intro le before result after run dead
  cases stmts with
  | nil =>
    rw [lowerStmts, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨dead, rfl, rfl⟩
  | cons stmt rest =>
    simp only [lowerStmts, bind_run, isLive_none dead, Bool.false_eq_true, ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨dead, rfl, rfl⟩

mutual

theorem stopped_lowerExpr : ∀ e : Expr, StoppedGraph (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExprs es) fun _ => stopped_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact stopped_emitDef _
  | .bool b => by simp only [lowerExpr]; exact stopped_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerPlace p) fun _ => stopped_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerPlace p) fun r => stopped_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerView v) fun _ => StoppedGraph.bind (stopped_lowerBound lo) fun _ =>
      StoppedGraph.bind (stopped_lowerBound hi) fun _ => stopped_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerView v) fun _ => stopped_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun a => StoppedGraph.bind (stopped_intTyOf a) fun _ => stopped_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr a) fun x => StoppedGraph.bind (stopped_lowerExpr b) fun y =>
      StoppedGraph.bind (stopped_intTyOf x) fun _ => stopped_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine StoppedGraph.bind (stopped_lowerExpr a) fun x => StoppedGraph.bind (stopped_lowerExpr b) fun y =>
      StoppedGraph.bind (stopped_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact stopped_emitDef _
    | view _ _ => exact stopped_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr a) fun x => stopped_shortCircuit true x (lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr a) fun x => stopped_shortCircuit false x (lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => stopped_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun a => StoppedGraph.bind (stopped_intTyOf a) fun _ => stopped_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerArgs args) fun _ =>
      StoppedGraph.bind (stopped_emitDef _) fun r => StoppedGraph.bind stopped_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact StoppedGraph.pure _ | exact StoppedGraph.bind (stopped_emitTerm _) fun _ => StoppedGraph.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerPlace owner) fun r => StoppedGraph.bind (stopped_lowerExpr e) fun v =>
      stopped_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerPlace owner) fun _ => stopped_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr c) fun cv =>
      stopped_whenLive _ _
  | .blockE b => by
    simp only [lowerExpr]
    exact stopped_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExprs es) fun _ => stopped_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => stopped_emitDef _

theorem stopped_lowerExprs : ∀ es : List Expr, StoppedGraph (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact StoppedGraph.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => StoppedGraph.bind (stopped_lowerExprs rest) fun _ => StoppedGraph.pure _

theorem stopped_lowerArg : ∀ a : Arg, StoppedGraph (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact stopped_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact StoppedGraph.bind (stopped_lowerPlace p) fun r => stopped_borrowTo m r

theorem stopped_lowerArgs : ∀ as : List Arg, StoppedGraph (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact StoppedGraph.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact StoppedGraph.bind (stopped_lowerArg a) fun _ => StoppedGraph.bind (stopped_lowerArgs rest) fun _ => StoppedGraph.pure _

theorem stopped_lowerPlace : ∀ p : Place, StoppedGraph (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact StoppedGraph.bind (stopped_lowerPlace owner) fun _ => stopped_emitDef _
  | .var x => by simp only [lowerPlace]; exact stopped_emitDef _
  | .global g => by simp only [lowerPlace]; exact stopped_emitDef _
  | .deref e => by simp only [lowerPlace]; exact stopped_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact StoppedGraph.bind (stopped_lowerView v) fun _ => StoppedGraph.bind (stopped_lowerExpr i) fun _ => stopped_emitDef _

theorem stopped_lowerView : ∀ v : View, StoppedGraph (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact StoppedGraph.bind (stopped_lowerPlace p) fun _ => stopped_emitDef _
  | .val e => by
    simp only [lowerView]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => stopped_emitDef _

theorem stopped_lowerBound : ∀ b : Bound, StoppedGraph (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact StoppedGraph.pure _
  | .expr e => by
    simp only [lowerBound]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => StoppedGraph.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => StoppedGraph.pure _

theorem stopped_lowerEachSource : ∀ v : View, StoppedGraph (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact StoppedGraph.bind (stopped_lowerPlace p) fun _ => StoppedGraph.bind (stopped_emitDef _) fun _ => StoppedGraph.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact StoppedGraph.bind (stopped_lowerExpr e) fun _ => StoppedGraph.bind (stopped_emitDef _) fun _ => StoppedGraph.pure _

theorem stopped_lowerBlockValue (want : Bool) : ∀ v : Option Expr, StoppedGraph (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact stopped_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact StoppedGraph.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact stopped_emitDef _

theorem stopped_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, StoppedGraph (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact StoppedGraph.bind (stopped_emitEffect _) fun _ => stopped_inScope sc
      (StoppedGraph.bind (stopped_initSlots _) fun _ => StoppedGraph.bind (stopped_lowerStmts lc stmts) fun _ =>
        StoppedGraph.bind (stopped_lowerBlockValue want value) fun _ => StoppedGraph.bind (stopped_emitEffect _) fun _ =>
        StoppedGraph.pure _)

end

end Goose.Lower.Validation.SummaryPreservation
