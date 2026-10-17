import Goose.Lower.Validation.ExpressionTyping
import Goose.Lower.Validation.JoinTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def StaticBlockResult : Core.Block → Prop
  | .mk _ _ none => True
  | .mk _ _ (some e) => StaticExpression e

theorem lowerBlock_static_result_typed {env : Core.TEnv} {body : Core.Block}
    (supported : StaticBlockResult body) {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish))
    {lc : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)}
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock lc pre true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : after.vals[value]? = some (some (.data ty)) := by
  cases body with
  | mk scope statements expression =>
    unfold Core.tyBlock at source
    by_cases nested : scope ∈ env.scopes
    · simp [nested, chk] at source
    · simp only [List.contains_iff_mem, nested, ite_false] at source
      obtain ⟨declared, declaredFinish, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨finalEnv, valueStart, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      have declaredEnv := declarePre_lowerEnv declaration results
      have finalLower := tyStmts_lowerEnv statementsTyped results
      have sameEnv : lowerEnv finalEnv.mod finalEnv.vars results = lowerEnv env.mod env.vars results :=
        finalLower.trans declaredEnv
      simp only [lowerBlock, inScope] at run
      obtain ⟨_, entered, _, run⟩ := bind_eq.mp run
      obtain ⟨_, pushed, _, run⟩ := bind_eq.mp run
      obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
      obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
      obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
      subst after
      subst value
      obtain ⟨_, initialized, _, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, statementsAfter, _, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
      have poppedLive := dead_popScope.live_before popRun live
      have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
      have resultTyped : valueAfter.vals[result]? = some (some (.data ty)) := by
        cases expression with
        | none =>
          have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
          change ty = .unit at shape
          subst ty
          simp only [lowerBlockValue, ite_true] at valueRun
          have initial := (dead_emitDef .constUnit).live_before valueRun valueLive
          cases current : statementsAfter.cur with
          | none => simp [current] at initial
          | some block =>
            have recorded := emitDef_recorded (le := lowerEnv env.mod env.vars results)
              (op := .constUnit) current (show Op.resultTy (tyEnv (lowerEnv env.mod env.vars results) statementsAfter) .constUnit = .ok (.data .unit) from rfl)
            rw [valueRun] at recorded
            exact recorded.2.2.1
        | some e =>
          simp only [lowerBlockValue] at valueRun
          have initial := (dead_lowerExpr e).live_before valueRun valueLive
          cases current : statementsAfter.cur with
          | none => simp [current] at initial
          | some block =>
            have typed := lowerExpr_static_typed e supported source results statementsAfter current
            rw [sameEnv, valueRun] at typed
            exact typed.2
      have retained := types_emitEffect (.leave scope) _ _ _ _ leaveRun result (.data ty) resultTyped
      exact types_popScope _ _ _ _ popRun result (.data ty) retained

theorem lowerExpr_blockE_static_result_typed {env : Core.TEnv} {body : Core.Block}
    (supported : StaticBlockResult body) {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.blockE body) start = .ok (ty, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr (.blockE body) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : after.vals[value]? = some (some (.data ty)) := by
  exact lowerBlock_static_result_typed (env := Core.exprEnv env) supported source run live

theorem lowerPlace_deref_blockE_static_result_typed {env : Core.TEnv} {body : Core.Block}
    (supported : StaticBlockResult body) {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.deref (.blockE body)) start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace (.deref (.blockE body)) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child (show Core.sliceRefTy env (.blockE body) = none from rfl) source
  exact ⟨mu, lowerExpr_blockE_static_result_typed supported childSource run live⟩

theorem lowerExpr_and_source_result_typed {env : Core.TEnv} {left right : Expr}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.and left right) start = .ok (ty, finish))
    (results : List Ty) (before : LS) :
    let (value, after) := lowerExpr (.and left right) (lowerEnv env.mod env.vars results) before
    after.cur.isSome = true → after.vals[value]? = some (some (.data ty)) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  change ty = .bool at shape
  subst ty
  exact lowerExpr_and_result_typed left right _ before

theorem lowerExpr_or_source_result_typed {env : Core.TEnv} {left right : Expr}
    {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.or left right) start = .ok (ty, finish))
    (results : List Ty) (before : LS) :
    let (value, after) := lowerExpr (.or left right) (lowerEnv env.mod env.vars results) before
    after.cur.isSome = true → after.vals[value]? = some (some (.data ty)) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  change ty = .bool at shape
  subst ty
  exact lowerExpr_or_result_typed left right _ before

theorem lowerExpr_ifE_static_result_typed {env : Core.TEnv} {condition : Expr}
    {thenBody elseBody : Core.Block} (thenSupported : StaticBlockResult thenBody)
    (elseSupported : StaticBlockResult elseBody) {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.ifE condition thenBody elseBody) start = .ok (ty, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr (.ifE condition thenBody elseBody) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : after.vals[value]? = some (some (.data ty)) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨thenTy, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨elseTy, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases equal : (thenTy == elseTy) = true
  · simp only [equal, ite_true] at source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change ty = thenTy at shape
    have typesEqual : thenTy = elseTy := eq_of_beq equal
    subst elseTy
    subst ty
    simp only [lowerExpr] at run
    obtain ⟨conditionValue, middle, _, run⟩ := bind_eq.mp run
    cases current : middle.cur with
    | none =>
      rw [whenLive_none _ _ _ current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      simp [current] at live
    | some block =>
      rw [whenLive_some _ _ _ current] at run
      obtain ⟨arms, forked, _, run⟩ := bind_eq.mp run
      obtain ⟨_, thenStart, _, run⟩ := bind_eq.mp run
      obtain ⟨thenValue, thenAfter, thenRun, run⟩ := bind_eq.mp run
      obtain ⟨thenEnd, thenClosed, thenEndRun, run⟩ := bind_eq.mp run
      rw [curBlock_run] at thenEndRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj thenEndRun
      obtain ⟨_, elseStart, elseStartRun, run⟩ := bind_eq.mp run
      obtain ⟨elseValue, elseAfter, elseRun, run⟩ := bind_eq.mp run
      obtain ⟨elseEnd, elseClosed, elseEndRun, run⟩ := bind_eq.mp run
      rw [curBlock_run] at elseEndRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj elseEndRun
      have thenTyped : thenAfter.cur.isSome = true →
          elseAfter.vals[thenValue]? = some (some (.data thenTy)) := by
        intro branchLive
        have typed := lowerBlock_static_result_typed (env := Core.exprEnv env)
          thenSupported thenSource thenRun branchLive
        have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data thenTy) typed
        exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data thenTy) retained
      have elseTyped : elseAfter.cur.isSome = true →
          elseAfter.vals[elseValue]? = some (some (.data thenTy)) := by
        intro branchLive
        exact lowerBlock_static_result_typed (env := Core.exprEnv env)
          elseSupported elseSource elseRun branchLive
      have joined := joinValue_typed (le := lowerEnv env.mod env.vars results) thenTyped elseTyped
      rw [run] at joined
      exact joined live
  · simp only [equal] at source
    change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
      fun _ => pure thenTy) elseFinish = .ok (ty, finish) at source
    obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (rej_ok _ _ _ _).mp rejected |>.elim

end Goose.Lower.Validation
