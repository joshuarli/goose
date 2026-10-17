import Goose.Lower.Validation.SummaryPreservationReplayControlActions
import Goose.Lower.Validation.SummaryPreservationCoerceSlots
import Goose.Lower.Validation.SummaryPreservationRefinedResults
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem coerceTo_dead_state (type : Ty) (value : ValueId) (origin : OriginId)
    (le : LEnv) (ls : LS) (dead : ls.cur = none) :
    (coerceTo type value origin le ls).2 = ls := by
  rcases coerceTo_cases (r' := (coerceTo type value origin le ls).1) rfl with same | frozen | sliced
  · exact same.2
  · obtain ⟨_, _, run⟩ := frozen
    rw [emitDef_none _ _ dead] at run
    exact (congrArg Prod.snd run).symm
  · obtain ⟨_, view, middle, _, first, second⟩ := sliced
    rw [emitDef_none _ _ dead] at first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj first
    rw [emitDef_none _ _ dead] at second
    exact (congrArg Prod.snd second).symm

private theorem leaveAll_current (scopes : List ScopeId) (le : LEnv) (ls : LS) :
    (Goose.Lower.leaveAll scopes le ls).2.cur = ls.cur := by
  induction scopes generalizing ls with
  | nil => rfl
  | cons scope rest ih =>
    simp only [Goose.Lower.leaveAll, bind_run]
    rw [ih]
    cases current : ls.cur with
    | none => rw [emitEffect_none _ _ current]; exact current
    | some block => rw [emitEffect_run _ _ current]; exact current

private theorem leaveTo_current (depth : Nat) (le : LEnv) (ls : LS) :
    (Goose.Lower.leaveTo depth le ls).2.cur = ls.cur := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using leaveAll_current _ le ls

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem coerceResult (value : ValueId) (origin : OriginId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (input : ls.cur.isSome = true → value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.coerceResult value origin le ls).2 next ∧
      ((Goose.Lower.coerceResult value origin le ls).2.cur.isSome = true →
        (Goose.Lower.coerceResult value origin le ls).1 < (Goose.Lower.coerceResult value origin le ls).2.vals.size ∧
        RootsRefine func (rootsAt next.vals (Goose.Lower.coerceResult value origin le ls).1) sourceRoots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have same : (Goose.Lower.coerceResult value origin le ls).2 = ls := by
      simp only [Goose.Lower.coerceResult, bind_run, read_apply]
      cases destination : le.results.head? with
      | none => rfl
      | some type => exact coerceTo_dead_state type value origin le ls current
    rw [same]
    exact ⟨upper, ready, by simp [current], fun _ _ => rfl⟩
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    obtain ⟨next, roots, effects, refined, slotEq, symbols, selected, blockBound, valueBound, retained⟩ :=
      coerceResult_refined_witness_growth origin ready.symbols current (ready.current block current)
        ready.roots ready.effects (input live).1 (input live).2 originBound
    exact ⟨next, ⟨roots, effects, symbols, fun candidate row => by
      rw [selected] at row; cases row; exact blockBound, slotEq.trans ready.slotsEq⟩,
      fun _ => ⟨valueBound, refined⟩, retained⟩

theorem returnValue {sourceModule : Core.Module} {ctx : Context} {impl : Impl}
    {env : PEnv} {expression : Expr} {origin : OriginId} {sourceRoots : List RootRef}
    {initial : LS} {value : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
      target le scopeCount slots ls upper)
    (expressionRun : lowerExpr expression le initial = (value, ls))
    (input : ls.cur.isSome = true → value < ls.vals.size ∧
      RootsRefine (lowerContextAt sourceModule ctx impl) (rootsAt upper.vals value) sourceRoots)
    (sourceContext : env.mod = sourceModule ∧ env.ctx = ctx ∧ env.impl = impl)
    (contextOk : CtxOk env.mod env.impl env.ctx)
    (checkedResult : checkResultV env sourceRoots = .ok ())
    (originBound : origin < le.mod.origins.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ∃ next returned returnedState,
      Goose.Lower.coerceResult value origin le ls = (returned, returnedState) ∧
      lowerStmt loop (.ret (some expression) origin) le initial =
        Goose.Lower.emitTerm (.ret [returned] (some origin)) le (Goose.Lower.leaveTo 0 le returnedState).2 ∧
      ReplayBuilder module results vt (lowerContextAt sourceModule ctx impl)
        target le scopeCount slots (lowerStmt loop (.ret (some expression) origin) le initial).2 next ∧
      (returnedState.cur.isSome = true →
        ∀ root ∈ rootsAt next.vals returned,
          root ∈ refinedResultUpper (lowerContextAt sourceModule ctx impl) (ctx.resultRoots[0]?.getD [])) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, coercedReady, returnedFacts, retained⟩ := ready.coerceResult value origin sourceRoots input originBound
  let coerced := Goose.Lower.coerceResult value origin le ls
  have whole : lowerStmt loop (.ret (some expression) origin) le initial =
      Goose.Lower.emitTerm (.ret [coerced.1] (some origin)) le (Goose.Lower.leaveTo 0 le coerced.2).2 := by
    simp only [lowerStmt, bind_run, expressionRun, pure_run, coerced]
  have coercedStack : coerced.2.stack = ls.stack := (advB_coerceResult value origin le ls _ _ rfl).stack
  have left := coercedReady.leaveTo 0 (by
    change ∀ scope ∈ coerced.2.stack, scope < scopeCount
    rw [coercedStack]
    exact scopes)
  have leftGrowth := advB_leaveTo 0 le coerced.2 _ _ rfl
  have emitted := left.emitTerm (.ret [coerced.1] (some origin))
    (by
      intro live
      apply Inst.SymbolsWithin.term
      · have originalLive : coerced.2.cur.isSome = true := by
          simpa only [leaveTo_current] using live
        intro operand member
        have same : operand = coerced.1 := List.mem_singleton.mp member
        subst operand
        exact Nat.lt_of_lt_of_le (returnedFacts originalLive).1 leftGrowth.vals
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (by intros; trivial) (by intros; exact effectRefinement_empty _ _)
  refine ⟨next, coerced.1, coerced.2, rfl, whole, ?_, ?_, retained⟩
  · rw [whole]
    exact emitted
  · intro live
    have refined := (returnedFacts live).2
    have same : lowerContextAt sourceModule ctx impl = lowerContextAt env.mod env.ctx env.impl := by
      rw [sourceContext.1, sourceContext.2.1, sourceContext.2.2]
    rw [same] at refined
    have result := checkedResult_refinedResultUpper contextOk refined checkedResult
    simpa only [sourceContext.1, sourceContext.2.1, sourceContext.2.2] using result

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
