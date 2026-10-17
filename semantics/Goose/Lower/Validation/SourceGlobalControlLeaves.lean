import Goose.Lower.Validation.SourceGlobalControlContracts
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon
import Goose.Lower.Validation.SummaryPreservationReplayControl
import Goose.Lower.Validation.SummaryPreservationReturnLedgerSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem global_statement_transfer {typingEnv output : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {initial : LS} {upper next : Prov} {scope start finish : Nat} {statement : Stmt}
    (expected : List RootRef) (loop : Option LoopCtx) (inside : typingEnv.inExpr = true)
    (typed : tyStmt typingEnv scope statement start = .ok (output, finish))
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper)
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected initial upper
      (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next :=
  ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
    (returnFrame_lowerStmt loop statement (tyStmt_returnFree_of_plain_or_inExpr statement typed (Or.inl inside)) _ _ _ _ rfl)

theorem global_statement_plain_transfer {typingEnv output : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {initial : LS} {upper next : Prov} {scope start finish : Nat} {statement : Stmt}
    (expected : List RootRef) (loop : Option LoopCtx)
    (typed : tyStmt typingEnv scope statement start = .ok (output, finish)) (plain : statement.isPlain = true)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper)
    (retained : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) :
    ReturnBoundsPreserved expected initial upper
      (lowerStmt loop statement (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next :=
  ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
    (returnFrame_lowerStmt loop statement (tyStmt_returnFree_of_plain_or_inExpr statement typed (Or.inr plain)) _ _ _ _ rfl)

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}

theorem globalStatementReplay_expression {expression : Expr} {origin : OriginId}
    (child : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.expr expression origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  obtain ⟨next, completed, retained⟩ := ready.typedExpressionStatement loop typed replay ceiling (by
    intro type roots value state source replayed run effect input
    have childNative : NativeRows vt state := by
      simpa only [lowerStmt, bind_run, run, pure_run] using native
    obtain ⟨next, nextReady, valueInfo, retained⟩ :=
      child type start finish before after roots source replayed effect input generated (by simpa only [run] using childNative)
    rw [run] at nextReady
    exact ⟨next, nextReady, retained⟩)
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

theorem globalStatementReplay_returnUnit {origin : OriginId}
    (tables : SourceRootTables typingEnv env) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.ret none origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have bounded := stack (tyStmt_returnUnit_facts typed).1
  have completed := ready.returnUnit loop typed replay (tables.mutation_origin_bound typed) bounded
  refine ⟨upper, completed, (fun _ _ => rfl), ?_⟩
  intro expected declared subset prior
  exact prior.return_unit loop ready.current


theorem globalStatementReplay_break {origin : OriginId} :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.brk origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have completed : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots
      (lowerStmt loop (.brk origin) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 upper := by
    cases loop with
    | none => exact ready
    | some context =>
      have left := ready.leaveToScopes context.depth loopReplay.2
      exact left.loopBranch context.breakTo []
        (Nat.lt_of_lt_of_le loopBounds.1 (advB_leaveTo context.depth _ initial _ _ rfl).ext.1)
        (by simp) (by simp)
  refine ⟨upper, completed, (fun _ _ => rfl), ?_⟩
  intro expected
  exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize (fun _ _ => rfl)
    (returnFrame_lowerStmt loop (.brk origin) trivial _ initial _ _ rfl)

theorem globalStatementReplay_continue {origin : OriginId} :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.cont origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopBounds loopReplay native
  have nextState : ∃ next,
      ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmt loop (.cont origin) (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
    cases loop with
    | none => exact ⟨upper, ready, fun _ _ => rfl⟩
    | some context =>
      let le := lowerEnv env.mod env.impl.vars returnTypes
      let left := (Goose.Lower.leaveTo context.depth le initial).2
      have leftReady := ready.leaveToScopes context.depth loopReplay.2
      have growth := advB_leaveTo context.depth le initial _ _ rfl
      cases continuation : context.cont with
      | jump header =>
        have branched := leftReady.loopBranch header []
          (Nat.lt_of_lt_of_le (by simpa only [LoopBuilderTargets, continuation] using loopBounds.2) growth.ext.1)
          (by simp) (by simp)
        exact ⟨upper, by simpa only [lowerStmt, bind_run, continuation] using branched, fun _ _ => rfl⟩
      | next header type counter =>
        have headerBound : header < initial.blocks.size := by
          simpa only [LoopBuilderTargets, continuation] using loopBounds.2
        have counterBound : counter < initial.vals.size := by
          simpa only [continuation] using loopReplay.1
        obtain ⟨next, completed, retained⟩ := leftReady.loopRangeBack type counter header
          (Nat.lt_of_lt_of_le headerBound growth.ext.1) (Nat.lt_of_lt_of_le counterBound growth.vals)
        refine ⟨next, ?_, retained⟩
        have whole : lowerStmt (some context) (.cont origin) le initial =
            rangeBack type counter header le left := by
          simp only [lowerStmt, bind_run, continuation]
          change Goose.Lower.emitTerm (.br header [(emitDef (.next type counter) le left).1]) le
            (emitDef (.next type counter) le left).2 = rangeBack type counter header le left
          cases current : left.cur with
          | none => simp only [rangeBack, bind_run, isLive_none current, Bool.false_eq_true, ite_false,
              emitDef_none _ _ current, emitTerm_none _ _ current, pure_run]
          | some block => simp only [rangeBack, bind_run, isLive_run current, ite_true]
        rw [whole]
        exact completed
  obtain ⟨next, completed, retained⟩ := nextState
  exact ⟨next, completed, retained,
    fun expected => ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
      (returnFrame_lowerStmt loop (.cont origin) trivial _ initial _ _ rfl)⟩

#print axioms globalStatementReplay_break
#print axioms globalStatementReplay_continue
#print axioms globalStatementReplay_expression
#print axioms globalStatementReplay_returnUnit

end Goose.Lower.Validation.SummaryPreservation
