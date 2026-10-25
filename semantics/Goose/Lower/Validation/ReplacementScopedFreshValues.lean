import Goose.Lower.Validation.ReplacementScopedFreshActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem freshValue_lowerExpr : ∀ expr : Expr, FreshValueRun (lowerExpr expr)
  | .lit _ _ | .bool _ => freshValue_emitDef _
  | .structLit _ values | .arrLit _ values => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerExprs values) fun _ => freshValue_emitDef _
  | .read place => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerPlace place) fun _ =>
      FreshValueRun.post (freshValue_emitDef _) fun value => dead_recordReadValueRootRecipe value place
  | .ref mu place => freshValue_borrowTo (freshValue_lowerPlace place) (advB_lowerPlace place) mu
  | .slice _ view lo hi _ => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerView view) fun _ =>
      FreshValueRun.prepend (advB_lowerBound lo) fun _ =>
        FreshValueRun.prepend (advB_lowerBound hi) fun _ => freshValue_emitDef _
  | .len view => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerView view) fun _ => freshValue_emitDef _
  | .un _ child _ | .conv _ _ child _ => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerExpr child) fun value =>
      FreshValueRun.prepend (advB_intTyOf value) fun _ => freshValue_emitDef _
  | .bin _ left right _ => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerExpr left) fun value =>
      FreshValueRun.prepend (advB_lowerExpr right) fun _ =>
        FreshValueRun.prepend (advB_intTyOf value) fun _ => freshValue_emitDef _
  | .cmp _ left right => by
    simp only [lowerExpr]
    refine FreshValueRun.prepend (advB_lowerExpr left) fun value =>
      FreshValueRun.prepend (advB_lowerExpr right) fun _ =>
        FreshValueRun.prepend (advB_valTy value) fun type => ?_
    cases type with
    | data type => cases type <;> exact freshValue_emitDef _
    | view _ _ => exact freshValue_emitDef _
  | .and left right | .or left right => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerExpr left) fun value => freshValue_shortCircuit _ value _
  | .not child | .fill _ child => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerExpr child) fun _ => freshValue_emitDef _
  | .push owner child _ => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerPlace owner) fun _ =>
      FreshValueRun.prepend (advB_lowerExpr child) fun _ => freshValue_emitDef _
  | .pop owner _ => by
    simp only [lowerExpr]
    exact FreshValueRun.prepend (advB_lowerPlace owner) fun _ => freshValue_emitDef _
  | .call context args origin => by
    simp only [lowerExpr]
    apply FreshValueRun.prepend (advB_lowerArgs args)
    intro values env before value after run live
    obtain ⟨result, emitted, emission, le, loaded, loading, remaining⟩ :=
      (by simpa only [bind_eq] using run)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj loading
    cases returns : env.mod.noReturn context
    · simp only [returns, Bool.false_eq_true, ↓reduceIte] at remaining
      obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
      exact freshValue_emitDef _ _ _ _ _ emission live
    · simp only [returns, ↓reduceIte, bind_eq] at remaining
      obtain ⟨_, closed, closing, pureRun⟩ := remaining
      obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
      cases current : emitted.cur with
      | none =>
        rw [emitTerm_none _ _ current] at closing
        obtain ⟨_, rfl⟩ := Prod.mk.inj closing
        simp [current] at live
      | some block =>
        rw [emitTerm_run _ _ current] at closing
        obtain ⟨_, rfl⟩ := Prod.mk.inj closing
        simp at live
  | .ifE condition yes no => by
    simp only [lowerExpr]
    apply FreshValueRun.prepend (advB_lowerExpr condition)
    intro conditionValue
    apply freshValue_whenLive
    intro block
    exact FreshValueRun.prepend (advB_fork conditionValue) fun ⟨thenBlock, elseBlock⟩ =>
      FreshValueRun.prepend_sameValues (first := setCur (some thenBlock)) (by intros; rw [setCur_run]) fun _ =>
        FreshValueRun.prepend (advB_lowerBlock none [] true yes) fun thenValue =>
          FreshValueRun.prepend advB_curBlock fun thenEnd =>
            FreshValueRun.prepend_sameValues (first := setCur (some elseBlock)) (by intros; rw [setCur_run]) fun _ =>
              FreshValueRun.prepend (advB_lowerBlock none [] true no) fun elseValue =>
                FreshValueRun.prepend advB_curBlock fun elseEnd =>
                  FreshValueRun.post (freshValue_joinValue thenEnd elseEnd thenValue elseValue)
                    fun value => dead_recordValueRootRecipe value (sourceBlockScope yes)
  | .blockE body => freshValue_lowerBlock none [] body

theorem freshValue_lowerPlace : ∀ place : Place, FreshValueRun (lowerPlace place)
  | .var _ | .global _ => freshValue_emitDef _
  | .field owner _ => by
    simp only [lowerPlace]
    exact FreshValueRun.prepend (advB_lowerPlace owner) fun _ => freshValue_emitDef _
  | .elem view index _ => by
    simp only [lowerPlace]
    exact FreshValueRun.prepend (advB_lowerView view) fun _ =>
      FreshValueRun.prepend (advB_lowerExpr index) fun _ => freshValue_emitDef _
  | .deref expr => freshValue_lowerExpr expr

theorem freshValue_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) :
    ∀ body : Core.Block, FreshValueRun (lowerBlock context pre true body)
  | .mk scope statements value => by
    simp only [lowerBlock]
    apply FreshValueRun.prepend (advB_emitEffect (.enter scope))
    intro _
    apply FreshValueRun.inScope
    apply FreshValueRun.prepend (advB_initSlots pre)
    intro _
    apply FreshValueRun.prepend (advB_lowerStmts context statements)
    intro _
    apply FreshValueRun.post (next := fun _ => emitEffect (.leave scope))
    · cases value with
      | none => exact freshValue_emitDef _
      | some expr => exact freshValue_lowerExpr expr
    · intro _; exact dead_emitEffect _

end

theorem freshValue_lowerView (view : View) : FreshValueRun (lowerView view) := by
  cases view with
  | of place =>
    exact FreshValueRun.prepend (advB_lowerPlace place) fun _ => freshValue_emitDef _
  | val expr =>
    exact FreshValueRun.prepend (advB_lowerExpr expr) fun _ => freshValue_emitDef _

theorem freshValue_lowerArg (arg : Arg) : FreshValueRun (lowerArg arg) := by
  cases arg with
  | byVal expr => exact freshValue_lowerExpr expr
  | byRef mu place => exact freshValue_borrowTo (freshValue_lowerPlace place) (advB_lowerPlace place) mu

def FreshValueListRun (action : B (List ValueId)) : Prop :=
  ∀ env before values after, action env before = (values, after) →
    after.cur.isSome = true → ∀ value ∈ values, before.vals.size ≤ value

theorem freshValue_cons {head : B ValueId} {tail : B (List ValueId)}
    (freshHead : FreshValueRun head) (freshTail : FreshValueListRun tail)
    (advance : AdvB head) (dead : DeadRun tail) :
    FreshValueListRun (do let value ← head; let values ← tail; pure (value :: values)) := by
  intro env before values after run live value member
  obtain ⟨first, middle, firstRun, rest, last, tailRun, pureRun⟩ :=
    (by simpa only [bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  rcases List.mem_cons.mp member with rfl | member
  · exact freshHead _ _ _ _ firstRun (live_before dead tailRun live)
  · exact Nat.le_trans (advance _ _ _ _ firstRun).vals
      (freshTail _ _ _ _ tailRun live value member)

theorem freshValues_lowerExprs : ∀ expressions : List Expr, FreshValueListRun (lowerExprs expressions)
  | [] => by
    intro env before values after run live value member
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp at member
  | expr :: rest => by
    simp only [lowerExprs]
    exact freshValue_cons (freshValue_lowerExpr expr) (freshValues_lowerExprs rest)
      (advB_lowerExpr expr) (dead_lowerExprs rest)

theorem freshValues_lowerArgs : ∀ args : List Arg, FreshValueListRun (lowerArgs args)
  | [] => by
    intro env before values after run live value member
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp at member
  | arg :: rest => by
    simp only [lowerArgs]
    exact freshValue_cons (freshValue_lowerArg arg) (freshValues_lowerArgs rest)
      (advB_lowerArg arg) (dead_lowerArgs rest)

theorem freshValues_lowerBound (bound : Bound) {env before result after}
    (run : lowerBound bound env before = (result, after)) (live : after.cur.isSome = true) :
    ∀ value ∈ result.uses, before.vals.size ≤ value := by
  cases bound with
  | omitted =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp [Bnd.uses]
  | expr expr | fromEnd expr =>
    simp only [lowerBound, bind_eq] at run
    obtain ⟨value, middle, expression, remaining⟩ := run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
    intro used member
    have same : used = value := by simpa [Bnd.uses] using member
    subst used
    exact freshValue_lowerExpr expr _ _ _ _ expression live

theorem lowerExpr_freshInterval (expr : Expr) {env before value after}
    (run : lowerExpr expr env before = (value, after)) (live : after.cur.isSome = true) :
    before.vals.size ≤ value ∧ value < after.vals.size :=
  ⟨freshValue_lowerExpr expr env before value after run live,
    value_lowerExpr expr env before value after run live⟩

theorem lowerPlace_freshInterval (place : Place) {env before value after}
    (run : lowerPlace place env before = (value, after)) (live : after.cur.isSome = true) :
    before.vals.size ≤ value ∧ value < after.vals.size :=
  ⟨freshValue_lowerPlace place env before value after run live,
    value_lowerPlace place env before value after run live⟩

theorem lowerView_freshInterval (view : View) {env before value after}
    (run : lowerView view env before = (value, after)) (live : after.cur.isSome = true) :
    before.vals.size ≤ value ∧ value < after.vals.size :=
  ⟨freshValue_lowerView view env before value after run live,
    value_lowerView view env before value after run live⟩

#print axioms freshValue_lowerExpr
#print axioms freshValue_lowerPlace
#print axioms freshValue_lowerBlock
#print axioms freshValue_lowerView
#print axioms freshValues_lowerExprs
#print axioms freshValues_lowerArgs
#print axioms freshValues_lowerBound
#print axioms lowerExpr_freshInterval
#print axioms lowerPlace_freshInterval
#print axioms lowerView_freshInterval

end Goose.Lower.Validation
