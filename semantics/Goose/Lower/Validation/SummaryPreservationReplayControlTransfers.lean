import Goose.Lower.Validation.SummaryPreservationReplayControlReturns
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem typedExpressionStatement {env output : TEnv} {penv : PEnv} {expression : Expr}
    {origin : OriginId} {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.expr expression origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.expr expression origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (child : ∀ type roots value state,
      tyExpr env expression start = .ok (type, finish) →
      rpExpr penv expression before = .ok (roots, after) →
      lowerExpr expression le ls = (value, state) →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots ls upper →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots state next ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.expr expression origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨type, typed, _⟩ := tyStmt_expr_children source
  obtain ⟨roots, middle, expressionReplay, returned⟩ := (st_bind_ok _ _ _ _).mp replayed
  have same := (st_pure_ok _ _ _).mp returned
  have stateEq : after = middle := congrArg Prod.snd same
  subst after
  obtain ⟨next, generated, retained⟩ := child type roots _ _ typed expressionReplay rfl wholeEffect ready
  exact ⟨next, generated, retained⟩

theorem returnUnit {env output : TEnv} {penv : PEnv} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.ret none origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.ret none origin) before = .ok ((), after))
    (originBound : origin < le.mod.origins.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.ret none origin) le ls).2 upper := by
  have _ := tyStmt_returnUnit_facts source
  have _ : ((), after) = ((), before) := (st_pure_ok _ _ _).mp replayed
  have left := ready.leaveTo 0 scopes
  have returned := left.emitTerm (.ret [] (some origin))
    (by
      intros
      apply Inst.SymbolsWithin.term
      · simp [Term.uses]
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (by intros; trivial) (by intros; exact effectRefinement_empty func target)
  simpa only [lowerStmt, bind_run, pure_run] using returned

theorem breakStatement {env output : TEnv} {penv : PEnv} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.brk origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.brk origin) before = .ok ((), after))
    (destination : loop.breakTo < ls.blocks.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt (some loop) (.brk origin) le ls).2 upper := by
  have _ := tyStmt_break_facts source
  have _ : ((), after) = ((), before) := (st_pure_ok _ _ _).mp replayed
  have left := ready.leaveTo loop.depth scopes
  have bound : loop.breakTo < (Goose.Lower.leaveTo loop.depth le ls).2.blocks.size :=
    Nat.lt_of_lt_of_le destination (advB_leaveTo loop.depth le ls _ _ rfl).ext.1
  have branched := left.loopBranch loop.breakTo [] bound (by simp) (by simp)
  exact branched

theorem continueStatement {env output : TEnv} {penv : PEnv} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} (loop : LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.cont origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.cont origin) before = .ok ((), after))
    (destination : match loop.cont with
      | .jump header => header < ls.blocks.size
      | .next header _ counter => header < ls.blocks.size ∧ counter < ls.vals.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt (some loop) (.cont origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have _ := tyStmt_continue_facts source
  have _ : ((), after) = ((), before) := (st_pure_ok _ _ _).mp replayed
  have left := ready.leaveTo loop.depth scopes
  have growth := advB_leaveTo loop.depth le ls _ _ rfl
  cases continuation : loop.cont with
  | jump header =>
    have bound : header < (Goose.Lower.leaveTo loop.depth le ls).2.blocks.size :=
      Nat.lt_of_lt_of_le (by simpa only [continuation] using destination) growth.ext.1
    have branched := left.loopBranch header [] bound (by simp) (by simp)
    exact ⟨upper, by simpa only [lowerStmt, bind_run, continuation] using branched, fun _ _ => rfl⟩
  | next header type counter =>
    have bounds : header < ls.blocks.size ∧ counter < ls.vals.size := by simpa only [continuation] using destination
    obtain ⟨next, generated, retained⟩ := left.loopRangeBack type counter header
      (Nat.lt_of_lt_of_le bounds.1 growth.ext.1) (Nat.lt_of_lt_of_le bounds.2 growth.vals)
    refine ⟨next, ?_, retained⟩
    have same : lowerStmt (some loop) (.cont origin) le ls =
        rangeBack type counter header le (Goose.Lower.leaveTo loop.depth le ls).2 := by
      simp only [lowerStmt, bind_run, continuation]
      cases current : (Goose.Lower.leaveTo loop.depth le ls).2.cur with
      | none => simp only [rangeBack, bind_run, isLive_none current, Bool.false_eq_true, ite_false,
          emitDef_none _ _ current, emitTerm_none _ _ current, pure_run]
      | some block => simp only [rangeBack, bind_run, isLive_run current, ite_true]
    rw [same]
    exact generated

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
