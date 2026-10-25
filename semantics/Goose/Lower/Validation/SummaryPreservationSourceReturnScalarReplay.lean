import Goose.Lower.Validation.SummaryPreservationSourceReturnScalar
import Goose.Lower.Validation.SummaryPreservationReplayControlReturns
import Goose.Lower.Validation.ScopeUnwindActions

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem coerceResultScalar {actual expected : Ty} {value : ValueId} {origin : OriginId}
    {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (result : le.results.head? = some expected)
    (passable : actual.passableTo expected = true) (nonref : expected.isRefLike = false)
    (input : ls.cur.isSome = true → ReplayValue func upper ls value sourceRoots (.data actual)) :
    ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.coerceResult value origin le ls).2 upper ∧
      ((Goose.Lower.coerceResult value origin le ls).2.cur.isSome = true →
        ReplayValue func upper (Goose.Lower.coerceResult value origin le ls).2
          (Goose.Lower.coerceResult value origin le ls).1 sourceRoots (.data expected)) ∧
      Goose.Lower.coerceResult value origin le ls = (value, ls) := by
  have same := coerceResult_nonref_identity value origin le ls result nonref
  rw [same]
  refine ⟨ready, ?_, rfl⟩
  intro live
  have child := input live
  exact ⟨child.bound, child.refined, fun _ => child.scalar (passable_nonref_source passable nonref)⟩

theorem returnScalarValue {actual expected : Ty} {expression : Expr} {origin : OriginId}
    {sourceRoots : List RootRef} {initial : LS} {value : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (expressionRun : lowerExpr expression le initial = (value, ls))
    (result : le.results.head? = some expected)
    (passable : actual.passableTo expected = true) (nonref : expected.isRefLike = false)
    (input : ls.cur.isSome = true → ReplayValue func upper ls value sourceRoots (.data actual))
    (originBound : origin < le.mod.origins.size)
    (scopes : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.ret (some expression) origin) le initial).2 upper ∧
      Goose.Lower.coerceResult value origin le ls = (value, ls) ∧
      lowerStmt loop (.ret (some expression) origin) le initial =
        Goose.Lower.emitTerm (.ret [value] (some origin)) le (Goose.Lower.leaveTo 0 le ls).2 ∧
      (ls.cur.isSome = true → rootsAt upper.vals value = []) := by
  obtain ⟨_, returnedValue, coercedRun⟩ := ready.coerceResultScalar (origin := origin) result passable nonref input
  have whole : lowerStmt loop (.ret (some expression) origin) le initial =
      Goose.Lower.emitTerm (.ret [value] (some origin)) le (Goose.Lower.leaveTo 0 le ls).2 := by
    simp only [lowerStmt, bind_run, expressionRun, coercedRun, pure_run]
  have left := ready.leaveTo 0 scopes
  have leftGrowth := advB_leaveTo 0 le ls _ _ rfl
  have originalLive (live : (Goose.Lower.leaveTo 0 le ls).2.cur.isSome = true) : ls.cur.isSome = true := by
    cases current : ls.cur with
    | none => rw [leaveTo_none 0 le ls current] at live; simp [current] at live
    | some block => rfl
  have emitted := left.emitTerm (.ret [value] (some origin))
    (by
      intro live
      apply Inst.SymbolsWithin.term
      · intro operand member
        have same : operand = value := List.mem_singleton.mp member
        subst operand
        exact Nat.lt_of_lt_of_le (input (originalLive live)).bound leftGrowth.vals
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (by intros; trivial) (by intros; exact effectRefinement_empty func target)
  refine ⟨?_, coercedRun, whole, ?_⟩
  · rw [whole]
    exact emitted
  · intro live
    rw [coercedRun] at returnedValue
    exact (returnedValue live).scalar nonref

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
