import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem passable_nonref_source {actual expected : Ty}
    (passable : actual.passableTo expected = true) (nonref : expected.isRefLike = false) :
    actual.isRefLike = false := by
  cases actual <;> cases expected <;> simp_all [Ty.passableTo, Ty.isRefLike]

theorem coerceTo_nonref_identity {expected : Ty} (value : ValueId) (origin : OriginId)
    (env : LEnv) (state : LS) (nonref : expected.isRefLike = false) :
    coerceTo expected value origin env state = (value, state) := by
  cases expected <;> simp_all only [Ty.isRefLike, Bool.true_eq_false]
  all_goals simp only [coerceTo, bind_run, valTy_run, pure_run]

theorem coerceResult_nonref_identity {expected : Ty} (value : ValueId) (origin : OriginId)
    (env : LEnv) (state : LS) (result : env.results.head? = some expected)
    (nonref : expected.isRefLike = false) :
    coerceResult value origin env state = (value, state) := by
  simp only [coerceResult, bind_run, read_apply, result]
  exact coerceTo_nonref_identity value origin env state nonref

theorem source_return_scalar_children {env output : TEnv} {impl : Impl}
    {expression : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : tyStmt env scope (.ret (some expression) origin) start = .ok (output, finish))
    (implementation : env.impl = some impl)
    (nonref : (impl.results[0]?).any Ty.isRefLike = false) :
    ∃ expected actual,
      impl.results.toList = [expected] ∧ expected.isRefLike = false ∧ actual.isRefLike = false ∧
      tyExpr env expression start = .ok (actual, finish) ∧ actual.passableTo expected = true := by
  obtain ⟨expected, actual, typedImpl, _, typedImplementation, resultTypes, typed, passable, _⟩ :=
    tyStmt_return_children source
  have same : typedImpl = impl := Option.some.inj (typedImplementation.symm.trans implementation)
  subst typedImpl
  have resultRow : impl.results[0]? = some expected := by
    rw [← Array.getElem?_toList, resultTypes]
    rfl
  have expectedNonref : expected.isRefLike = false := by simpa only [resultRow, Option.any_some] using nonref
  exact ⟨expected, actual, resultTypes, expectedNonref, passable_nonref_source passable expectedNonref, typed, passable⟩

theorem source_return_scalar_roots {env output : TEnv} {impl : Impl}
    {expression : Expr} {origin : OriginId} {scope start finish : Nat}
    {func : Func} {le : LEnv} {before after : LS} {upper next : Prov}
    {value returned : ValueId} {sourceRoots : List RootRef} {actual : Ty}
    (source : tyStmt env scope (.ret (some expression) origin) start = .ok (output, finish))
    (implementation : env.impl = some impl)
    (nonref : (impl.results[0]?).any Ty.isRefLike = false)
    (results : le.results = impl.results.toList)
    (typed : tyExpr env expression start = .ok (actual, finish))
    (child : before.cur.isSome = true → ReplayValue func upper before value sourceRoots (.data actual))
    (size : upper.vals.size = before.vals.size)
    (run : coerceResult value origin le before = (returned, after))
    (retained : ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (live : after.cur.isSome = true) : rootsAt next.vals returned = [] := by
  obtain ⟨expected, sourceType, resultTypes, expectedNonref, actualNonref, checked, _⟩ :=
    source_return_scalar_children source implementation nonref
  have typeEq : sourceType = actual := (Prod.mk.inj (Except.ok.inj (checked.symm.trans typed))).1
  subst sourceType
  have resultHead : le.results.head? = some expected := by rw [results, resultTypes]; rfl
  rw [coerceResult_nonref_identity value origin le before resultHead expectedNonref] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  have valueFacts := child live
  rw [retained value (by simpa only [size] using valueFacts.bound)]
  exact valueFacts.scalar actualNonref

end Goose.Lower.Validation.SummaryPreservation
