import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingSourceOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedSourceBound (env : Core.TEnv) (results : List Ty) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
  ∀ {initial before : LS}, GeneratedBuilderState before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerBound bound (lowerEnv env.mod env.vars results) before).2

theorem emitted_source_bound_omitted (env : Core.TEnv) (results : List Ty) :
    EmittedSourceBound env results .omitted := by
  intro start finish source initial before generated builder
  exact builder

theorem emitted_source_bound_expr {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedSourceExpression env results expr) : EmittedSourceBound env results (.expr expr) := by
  intro start finish source initial before generated builder
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact child childSource generated builder

theorem emitted_source_bound_fromEnd {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedSourceExpression env results expr) : EmittedSourceBound env results (.fromEnd expr) := by
  intro start finish source initial before generated builder
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact child childSource generated builder

theorem BoundTyped.emitted_bounds {state : LS} {bound : Bnd} (typed : BoundTyped state bound) :
    ∀ operand ∈ bound.uses, operand < state.vals.size := by
  cases bound with
  | omitted => intro operand member; simp [Bnd.uses] at member
  | val value | fromEnd value =>
    obtain ⟨type, row⟩ := typed
    intro operand member
    have same : operand = value := by simpa [Bnd.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp row).1

theorem emitted_source_slice_children {env : Core.TEnv} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    {element : Ty} {writable : Bool} {viewStart viewFinish lowFinish highFinish : Nat}
    (viewSource : Core.tyView env view viewStart = .ok ((element, writable), viewFinish))
    (lowSource : Core.tyBound env lo viewFinish = .ok ((), lowFinish))
    (highSource : Core.tyBound env hi lowFinish = .ok ((), highFinish))
    (viewResult : ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
      lowerView view (lowerEnv env.mod env.vars results) before = (value, after) → after.cur.isSome = true →
      ∃ actual, after.vals[value]? = some (some (.view actual element)) ∧ actual.atLeast requested = true)
    (viewChild : EmittedSourceView env results view) (lowChild : EmittedSourceBound env results lo)
    (highChild : EmittedSourceBound env results hi)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.slice requested view lo hi origin) (lowerEnv env.mod env.vars results) before).2 := by
  let le := lowerEnv env.mod env.vars results
  let vw := lowerView view le before
  let low := lowerBound lo le vw.2
  let high := lowerBound hi le low.2
  have viewBuilder := viewChild viewSource generated builder
  have viewGenerated : GeneratedBuilderState vw.2 := generated.lowerView view rfl
  have lowBuilder := lowChild lowSource viewGenerated viewBuilder
  have lowGenerated : GeneratedBuilderState low.2 := viewGenerated.lowerBound lo rfl
  have highBuilder := highChild highSource lowGenerated lowBuilder
  have rows : high.2.cur.isSome = true →
      ∃ actual, high.2.vals[vw.1]? = some (some (.view actual element)) ∧
        actual.atLeast requested = true ∧ BoundTyped high.2 low.1 ∧ BoundTyped high.2 high.1 := by
    intro active
    have lowLive := (dead_lowerBound hi).live_before rfl active
    have viewLive := (dead_lowerBound lo).live_before rfl lowLive
    obtain ⟨actual, viewTyped, permission⟩ := viewResult generated rfl viewLive
    have lowTyped := lowerBound_generated_typed lo lowSource (show lowerBound lo le vw.2 = low from rfl) lowLive viewGenerated
    have highTyped := lowerBound_generated_typed hi highSource (show lowerBound hi le low.2 = high from rfl) active lowGenerated
    exact ⟨actual, (types_lowerBound hi le low.2 _ _ rfl) _ _
      ((types_lowerBound lo le vw.2 _ _ rfl) _ _ viewTyped), permission,
      lowTyped.retained (types_lowerBound hi le low.2 _ _ rfl), highTyped⟩
  apply highBuilder.emitDef (.viewSlice requested vw.1 low.1 high.1 (some origin))
  · intro active
    obtain ⟨actual, viewTyped, permission, lowTyped, highTyped⟩ := rows active
    have viewCheck : (tyEnv le high.2).viewTy vw.1 = .ok (actual, element) := by
      simp [TyEnv.viewTy, TyEnv.valTy, tyEnv, viewTyped, pure, Except.pure, bind, Except.bind]
    refine ⟨.data (.slice requested element), ?_⟩
    change (Op.viewSlice requested vw.1 low.1 high.1 (some origin)).resultTy (tyEnv le high.2) = _
    have lowCheck := lowTyped.check (le := le)
    have highCheck := highTyped.check (le := le)
    simp only [Op.resultTy]
    rw [viewCheck]
    simp only [pure, Except.pure, bind, Except.bind, permission, ite_true, lowCheck, highCheck]
  · intro active operand member
    obtain ⟨actual, viewTyped, permission, lowTyped, highTyped⟩ := rows active
    have either : operand = vw.1 ∨ operand ∈ low.1.uses ∨ operand ∈ high.1.uses := by
      simpa [Op.uses, List.mem_append, or_assoc] using member
    rcases either with rfl | lowMember | highMember
    · exact (Array.getElem?_eq_some_iff.mp viewTyped).1
    · exact lowTyped.emitted_bounds operand lowMember
    · exact highTyped.emitted_bounds operand highMember

theorem emitted_source_slice {env : Core.TEnv} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : EmittedSourceView env results view) (lowChild : EmittedSourceBound env results lo)
    (highChild : EmittedSourceBound env results hi) :
    EmittedSourceExpression env results (.slice requested view lo hi origin) := by
  intro type start finish source initial before generated builder
  cases requested with
  | readOnly =>
    obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish,
      viewSource, lowSource, highSource, _⟩ := tyExpr_slice_children source
    exact emitted_source_slice_children .readOnly view lo hi origin viewSource lowSource highSource
      (fun generated run live => by
        obtain ⟨actual, row⟩ := lowerView_generated_typed view viewSource run live generated
        exact ⟨actual, row, by cases actual <;> rfl⟩) viewChild lowChild highChild generated builder
  | mutable =>
    obtain ⟨element, viewStart, viewFinish, lowFinish, highFinish,
      viewSource, lowSource, highSource, _⟩ := tyExpr_slice_mutable_children source
    exact emitted_source_slice_children .mutable view lo hi origin viewSource lowSource highSource
      (fun generated run live => ⟨.mutable,
        lowerView_generated_writable_typed view viewSource run live generated, rfl⟩)
      viewChild lowChild highChild generated builder

end Goose.Lower.Validation
