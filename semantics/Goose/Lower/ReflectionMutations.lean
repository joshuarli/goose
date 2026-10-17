import Goose.Lower.ReflectionEffects
import Goose.Lower.ReflectionNormal

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem normalEffectReflection {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cells : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St} {e : Effect}
    (post : Post cfg env cx ls fr lsk frk ptk cells) {le : LEnv}
    (emit : emitEffect e le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    {result : Type} {source : Nat → M result} (monotone : FuelMonotone source)
    (equal : execEff cx.fn frk e = source sourceFuel >>= fun _ => pure frk) :
    ReflectAtFuel fuel cx ptk frk (fun n => source n >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls1 fr' pt' []) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx ptk frk _ _ state
  | succ fuel =>
      have effect := leaf_eff_reflectAtFuel (fuel := fuel) (sourceFuel := sourceFuel)
        (state := state) post emit extension (source := source) equal
      have completed : ReflectAtFuel (fuel + 1) cx ptk frk
          (fun n => source n >>= fun _ => pure (Flow.normal .unit))
          (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls1 fr' pt' []) state := by
        refine effect.bind ?_ monotone (fun _ n k bound => MonoM.refl _)
        intro n value after pt' fr' sourceRun matched residual bound
        exact ReflectAtFuel.ret residual ⟨rfl, matched⟩
      exact completed

theorem normalStmtReflection_expr {fuel : Nat} {expression : Expr} {origin : OriginId}
    (child : ExprReflection fuel expression) : NormalStmtReflection fuel (.expr expression origin) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨resultId, middle, expressionRun, finish⟩ := lowering
  rw [pure_run] at finish
  have same : middle = after := congrArg Prod.snd finish
  subst middle
  have expressionReflection := child cfg env cx le ls after fr pt resultId state
    rel point expressionRun extension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine expressionReflection.bind (second := ?_)
      (mono₁ := fun n k bound => (monoAll n k bound).expr cfg env expression)
      (mono₂ := fun _ n k bound => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    exact ReflectAtFuel.ret residual ⟨rfl, post.sub (by simp)⟩
  exact composition.of_source (fun n => ⟨n + 1, by simp only [execStmt]⟩)

theorem normalStmtReflection_assign {fuel : Nat} {place : Place} {expression : Expr}
    {origin : OriginId} (placeChild : PlaceReflection fuel place)
    (expressionChild : ∀ residual, residual ≤ fuel → ExprReflection residual expression) :
    NormalStmtReflection fuel (.assign place expression origin) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, value, last, expressionRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr expression _ _ _ _ expressionRun)
  have first := placeChild cfg env cx le ls middle fr pt address state rel point placeRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalExpr n cfg env expression >>= fun value =>
          writeLoc location value >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine first.bind (second := ?_)
      (mono₁ := fun n k bound => (monoAll n k bound).place cfg env place)
      (mono₂ := fun location n k bound =>
        MonoM.bind ((monoAll n k bound).expr cfg env expression) (fun _ => MonoM.refl _))
    · intro n location next pt1 fr1 source post1 residual bound
      have second := expressionChild residual bound cfg env cx le middle last fr1 pt1 value next
        post1.rel post1.pp expressionRun lastExtension
      refine second.bind (second := ?_)
        (mono₁ := fun n k bound => (monoAll n k bound).expr cfg env expression)
        (mono₂ := fun _ n k bound => MonoM.refl _)
      intro k value' final pt2 fr2 source' post2 remaining remainingBound
      have combined := post1.comp post2
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have valueCell := combined.has (value, .val value') (by simp)
      have equal : execEff cx.fn fr2 (.store address value (some origin)) =
          writeLoc location value' >>= fun _ => pure fr2 := by
        simp only [execEff, getVal_of addressCell, getVal_of valueCell,
          Goose.Core.expectRef, bind_assoc, pure_bind]
      exact normalEffectReflection combined emit extension (source := fun _ => writeLoc location value')
        (by intro n m bound; exact MonoM.refl _)
        (sourceFuel := k) equal
  exact composition.of_source (fun n => ⟨n + 1, by simp only [execStmt]⟩)

theorem normalStmtReflection_clear {fuel : Nat} {place : Place} {origin : OriginId}
    (placeChild : PlaceReflection fuel place) : NormalStmtReflection fuel (.clear place origin) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitEffect emit)
  have first := placeChild cfg env cx le ls middle fr pt address state rel point placeRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        truncateLoc location 0 >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine first.bind (second := ?_)
      (mono₁ := fun n k bound => (monoAll n k bound).place cfg env place)
      (mono₂ := fun _ n k bound => MonoM.refl _)
    intro n location next pt' fr' source post residual bound
    have addressCell := post.has (address, .val (.ref location)) (by simp)
    have equal : execEff cx.fn fr' (.clear address (some origin)) =
        truncateLoc location 0 >>= fun _ => pure fr' := by
      simp only [execEff, getVal_of addressCell, Goose.Core.expectRef, bind_assoc, pure_bind]
    exact normalEffectReflection post emit extension (source := fun _ => truncateLoc location 0)
      (by intro k j bound; exact MonoM.refl _)
      (sourceFuel := n) equal
  exact composition.of_source (fun n => ⟨n + 1, by simp only [execStmt]⟩)

theorem normalStmtReflection_append {fuel : Nat} {place : Place} {view : View}
    {origin : OriginId} (placeChild : PlaceReflection fuel place)
    (viewChild : ∀ residual, residual ≤ fuel → ViewReflection residual view) :
    NormalStmtReflection fuel (.append place view origin) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, viewId, last, viewRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerView view _ _ _ _ viewRun)
  have first := placeChild cfg env cx le ls middle fr pt address state rel point placeRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalView n cfg env view >>= fun sourceView =>
          readRun sourceView >>= fun elements => checkedAppendLoc location elements origin >>= fun _ =>
            pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine first.bind (second := ?_)
      (mono₁ := fun n k bound => (monoAll n k bound).place cfg env place)
      (mono₂ := fun location n k bound =>
        MonoM.bind ((monoAll n k bound).view cfg env view) (fun _ => MonoM.refl _))
    · intro n location next pt1 fr1 source post1 residual bound
      have second := viewChild residual bound cfg env cx le middle last fr1 pt1 viewId next
        post1.rel post1.pp viewRun lastExtension
      refine second.bind (second := ?_)
        (mono₁ := fun n k bound => (monoAll n k bound).view cfg env view)
        (mono₂ := fun _ n k bound => MonoM.refl _)
      intro k sourceView final pt2 fr2 source' post2 remaining remainingBound
      have combined := post1.comp post2
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have viewCell := combined.has (viewId, .view sourceView) (by simp)
      have equal : execEff cx.fn fr2 (.append address viewId (some origin)) =
          (readRun sourceView >>= fun elements => checkedAppendLoc location elements origin) >>= fun _ =>
            pure fr2 := by
        simp only [execEff, getVal_of addressCell, getView_of viewCell, Goose.Core.expectRef,
          bind_assoc, pure_bind, Goose.Core.checkedAppendLoc, checkCapacityAtOrg,
          checkAppendCapacity, abortAtOrg, abortAt]
        rfl
      simpa only [bind_assoc] using
        (normalEffectReflection (fuel := remaining) combined emit extension
          (source := fun _ => readRun sourceView >>= fun elements => checkedAppendLoc location elements origin)
          (by intro n m bound; exact MonoM.refl _)
          (sourceFuel := k) equal)
  exact composition.of_source (fun n => ⟨n + 1, by simp only [execStmt]⟩)

theorem normalStmtReflection_popN {fuel : Nat} {place : Place} {count : Expr}
    {origin : OriginId} (placeChild : PlaceReflection fuel place)
    (countChild : ∀ residual, residual ≤ fuel → ExprReflection residual count) :
    NormalStmtReflection fuel (.popN place count origin) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, countId, last, countRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr count _ _ _ _ countRun)
  have first := placeChild cfg env cx le ls middle fr pt address state rel point placeRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalExpr n cfg env count >>= fun countValue => do
          let (_, count) ← expectInt countValue
          let length ← lengthLoc location
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          else do
            truncateLoc location (length - count.toNat)
            pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine first.bind (second := ?_)
      (mono₁ := fun n k bound => (monoAll n k bound).place cfg env place)
      (mono₂ := fun location n k bound =>
        MonoM.bind ((monoAll n k bound).expr cfg env count) (fun _ => MonoM.refl _))
    · intro n location next pt1 fr1 source post1 residual bound
      have second := countChild residual bound cfg env cx le middle last fr1 pt1 countId next
        post1.rel post1.pp countRun lastExtension
      refine second.bind (second := ?_)
        (mono₁ := fun n k bound => (monoAll n k bound).expr cfg env count)
        (mono₂ := fun _ n k bound => MonoM.refl _)
      intro k countValue final pt2 fr2 source' post2 remaining remainingBound
      have combined := post1.comp post2
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have countCell := combined.has (countId, .val countValue) (by simp)
      let sourceAction : M Flow := do
        let (_, count) ← expectInt countValue
        let length ← lengthLoc location
        if count < 0 || count > (length : Int) then abortAt .popNRange origin
        else do
          truncateLoc location (length - count.toNat)
          pure (Flow.normal .unit)
      cases countValue with
      | int type count =>
        let action : M Unit := do
          let length ← lengthLoc location
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          else truncateLoc location (length - count.toNat)
        have equal : execEff cx.fn fr2 (.popN address countId (some origin)) =
            action >>= fun _ => pure fr2 := by
          simp [execEff, getVal_of addressCell, getVal_of countCell, Goose.Core.expectRef,
            Goose.Core.expectInt, abortAtOrg, abortAt, action]
          funext s
          cases hlen : lengthLoc location s with
          | stop err next => simp [action, bind_apply, hlen, M.instMonad, M.bind', M.pure', Functor.map]
          | ok length next =>
            by_cases invalid : count < 0 ∨ count > (length : Int)
            · simp [action, bind_apply, hlen, invalid, M.stop, M.bind', M.pure', Functor.map]
            · simp [action, bind_apply, hlen, invalid]
        have reflected := normalEffectReflection (fuel := remaining) (state := final)
            combined emit extension
            (source := fun _ => action) (by intro n m bound; exact MonoM.refl _)
            (sourceFuel := k) equal
        have sameFunction : sourceAction = action >>= fun _ => pure (Flow.normal .unit) := by
          funext s
          cases hlen : lengthLoc location s with
          | stop err next =>
            simp [sourceAction, action, Goose.Core.expectInt, bind_apply, pure_apply, hlen,
              M.bind', M.pure', Functor.map]
          | ok length next =>
            by_cases invalid : count < 0 ∨ count > (length : Int)
            · simp [sourceAction, action, Goose.Core.expectInt, bind_apply, pure_apply, hlen,
                invalid, abortAt, M.stop, M.bind', M.pure', Functor.map]
            · cases htruncate : truncateLoc location (length - count.toNat) next <;>
                simp [sourceAction, action, Goose.Core.expectInt, bind_apply, pure_apply, hlen,
                  invalid, htruncate, M.bind', M.pure', Functor.map]
        have same := congrFun sameFunction final
        exact reflected.of_source (fun n => ⟨n, same⟩)
      | _ =>
        let action : M Unit := fault .shape
        have equal : execEff cx.fn fr2 (.popN address countId (some origin)) =
            action >>= fun _ => pure fr2 := by
          simp [execEff, getVal_of addressCell, getVal_of countCell, Goose.Core.expectRef,
            Goose.Core.expectInt, action, fault, M.bind', M.pure', Functor.map] <;> rfl
        have reflected := normalEffectReflection (fuel := remaining) (state := final)
            combined emit extension
            (source := fun _ => action) (by intro n m bound; exact MonoM.refl _)
            (sourceFuel := k) equal
        have same : sourceAction final = (action >>= fun _ => pure (Flow.normal .unit)) final := by
          simp [sourceAction, Goose.Core.expectInt, action, fault, M.stop, M.bind'] <;> rfl
        exact reflected.of_source (fun n => ⟨n, same⟩)
  exact composition.of_source (fun n => ⟨n + 1, by simp only [execStmt]⟩)

end Goose.Lower
