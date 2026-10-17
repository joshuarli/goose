import Goose.Lower.Validation.ExpressionContentsRulesSourceCases
import Goose.Lower.Validation.ExpressionContentsRulesSource
import Goose.Lower.Validation.ExpressionContentsRulesCall
import Goose.Lower.Validation.JoinContentsControl
import Goose.Lower.Validation.PermissionPreservationSourceTransfers
import Goose.Lower.Validation.ExpressionTypingRecursive
import Goose.Lower.Validation.ExpressionTypingSourceContents
import Goose.Lower.Validation.ExpressionTypingContentsChildren
import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.ExpressionTypingContentsPlaceOps
import Goose.Lower.Validation.ExpressionTypingContentsBorrow

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

local macro "generated_builder" : tactic => `(tactic| assumption)

private theorem generated_pushScope {before after : LS} (generated : GeneratedBuilderState before)
    {scope : ScopeId} {le : LEnv} {result : Unit}
    (run : pushScope scope le before = (result, after)) : GeneratedBuilderState after := by
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

private theorem generated_setCur_sizes {before after : LS} {le : LEnv} {current : Option BlockId}
    {result : Unit} (run : setCur current le before = (result, after)) :
    after.blocks.size = before.blocks.size ∧ after.vals.size = before.vals.size := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨rfl, rfl⟩

mutual

theorem lowerExpr_generated_typed (e : Expr)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env e start = .ok (ty, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr e (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : after.vals[value]? = some (some (.data ty)) := by
  cases e with
  | lit t n | bool b =>
    have initial := (dead_lowerExpr _).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerExpr_static_typed _ (by trivial) source results before current
      rw [run] at typed
      exact typed.2
  | read p =>
    obtain ⟨info, next, placeSource, shape⟩ := tyExpr_read_place source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, mid, placeRun, emitted⟩ := bind_eq.mp lowering
    have midLive := (dead_emitDef (.load address)).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_generated_typed p placeSource placeRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have loaded := lowerExpr_read_typed_of_place placeRun typed current
      rw [run] at loaded
      exact loaded.2
  | ref mu p =>
    cases mu with
    | mutable =>
      obtain ⟨info, placeFinish, placeSource, shape, permission⟩ := tyExpr_ref_place source
      have writable : info.referenceWritable env.mod.profile = true := by
        cases bound : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
      have lowering := run
      simp only [lowerExpr] at lowering
      obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
      have midLive := (dead_borrowTo .mutable address).live_before frozenRun live
      have typed := lowerPlace_generated_writable_typed p placeSource writable placeRun midLive
      cases current : mid.cur with
      | none => simp [current] at midLive
      | some block =>
        have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) (requested := .mutable) typed (by rfl) current
        rw [frozenRun] at frozen
        simpa only [shape] using frozen.2
    | readOnly =>
      obtain ⟨info, next, placeSource, shape, _⟩ := tyExpr_ref_place source
      subst ty
      have lowering := run
      simp only [lowerExpr] at lowering
      obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
      have midLive := (dead_borrowTo .readOnly address).live_before frozenRun live
      obtain ⟨actual, typed⟩ := lowerPlace_generated_typed p placeSource placeRun midLive
      cases current : mid.cur with
      | none => simp [current] at midLive
      | some block =>
        have permission : actual.atLeast .readOnly = true := by cases actual <;> rfl
        have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) typed permission current
        rw [frozenRun] at frozen
        exact frozen.2
  | un op e origin =>
    obtain ⟨childStart, childFinish, intTy, childSource, shape, signed⟩ := tyExpr_un_child source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨child, mid, childRun, tailRun⟩ := bind_eq.mp lowering
    have midLive := (DeadRun.bind (dead_intTyOf child) fun _ => dead_emitDef _).live_before tailRun live
    have typed := lowerExpr_generated_typed e childSource childRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have lowered := lowerExpr_un_typed_of_child (op := op) (origin := origin) childRun typed signed current
      rw [run] at lowered
      exact lowered.2
  | bin op a b origin =>
    obtain ⟨aStart, aFinish, bStart, bFinish, intTy, aSource, bSource, shape⟩ := tyExpr_bin_children source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨av, aState, aRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨bv, mid, bRun, tailRun⟩ := bind_eq.mp lowering
    have midLive := (DeadRun.bind (dead_intTyOf av) fun _ => dead_emitDef _).live_before tailRun live
    have aGenerated := generated.lowerExpr a aRun
    have bTyped := lowerExpr_generated_typed b bSource bRun midLive
    have aLive := (dead_lowerExpr b).live_before bRun midLive
    have aTyped := lowerExpr_generated_typed a aSource aRun aLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have lowered := lowerExpr_bin_typed_of_children (op := op) (origin := origin) aRun aTyped bRun bTyped current
      rw [run] at lowered
      exact lowered.2
  | not e =>
    obtain ⟨childFinish, childSource, shape⟩ := tyExpr_not_child source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨child, mid, childRun, emitted⟩ := bind_eq.mp lowering
    have midLive := (dead_emitDef (.boolNot child)).live_before emitted live
    have typed := lowerExpr_generated_typed e childSource childRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have lowered := lowerExpr_not_typed_of_child childRun typed current
      rw [run] at lowered
      exact lowered.2
  | len v =>
    simp only [Core.tyExpr] at source
    obtain ⟨pair, next, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change ty = .int .i64 at shape
    subst ty
    simp only [lowerExpr] at run
    obtain ⟨view, mid, viewRun, emitted⟩ := bind_eq.mp run
    have midLive := (dead_emitDef (.viewLen view)).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerView_generated_typed v viewSource viewRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have operation : (Op.viewLen view).resultTy (tyEnv (lowerEnv env.mod env.vars results) mid) = .ok (.data (.int .i64)) := by
        simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | slice mu view lo hi origin =>
    cases mu with
    | mutable =>
      obtain ⟨element, viewStart, viewFinish, lowFinish, highFinish,
        viewSource, lowSource, highSource, shape⟩ := tyExpr_slice_mutable_children source
      subst ty
      simp only [lowerExpr] at run
      obtain ⟨viewValue, viewAfter, viewRun, run⟩ := bind_eq.mp run
      obtain ⟨lowValue, lowAfter, lowRun, run⟩ := bind_eq.mp run
      obtain ⟨highValue, middle, highRun, emitted⟩ := bind_eq.mp run
      have middleLive := (dead_emitDef (.viewSlice .mutable viewValue lowValue highValue (some origin))).live_before emitted live
      have viewGenerated := generated.lowerView _ viewRun
      have lowGenerated := viewGenerated.lowerBound lo lowRun
      have highTyped := lowerBound_generated_typed hi highSource highRun middleLive
      have lowLive := (dead_lowerBound hi).live_before highRun middleLive
      have lowTyped := lowerBound_generated_typed lo lowSource lowRun lowLive
      have viewLive := (dead_lowerBound lo).live_before lowRun lowLive
      have viewTyped := lowerView_generated_writable_typed view viewSource viewRun viewLive
      have retainedLow := lowTyped.retained (types_lowerBound hi _ _ _ _ highRun)
      have retainedView := types_lowerBound hi _ _ _ _ highRun viewValue (.view .mutable element)
        (types_lowerBound lo _ _ _ _ lowRun viewValue (.view .mutable element) viewTyped)
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have operation := mutableSlice_resultTy (le := lowerEnv env.mod env.vars results)
          retainedView retainedLow highTyped origin
        have recorded := emitDef_recorded current operation
        rw [emitted] at recorded
        exact recorded.2.2.1
    | readOnly =>
      obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish,
        viewSource, lowSource, highSource, shape⟩ := tyExpr_slice_children source
      subst ty
      simp only [lowerExpr] at run
      obtain ⟨viewValue, viewAfter, viewRun, run⟩ := bind_eq.mp run
      obtain ⟨lowValue, lowAfter, lowRun, run⟩ := bind_eq.mp run
      obtain ⟨highValue, middle, highRun, emitted⟩ := bind_eq.mp run
      have middleLive := (dead_emitDef (.viewSlice .readOnly viewValue lowValue highValue (some origin))).live_before emitted live
      have viewGenerated := generated.lowerView _ viewRun
      have lowGenerated := viewGenerated.lowerBound lo lowRun
      have highTyped := lowerBound_generated_typed hi highSource highRun middleLive
      have lowLive := (dead_lowerBound hi).live_before highRun middleLive
      have lowTyped := lowerBound_generated_typed lo lowSource lowRun lowLive
      have viewLive := (dead_lowerBound lo).live_before lowRun lowLive
      obtain ⟨actual, viewTyped⟩ := lowerView_generated_typed view viewSource viewRun viewLive
      have retainedLow := lowTyped.retained (types_lowerBound hi _ _ _ _ highRun)
      have retainedView := types_lowerBound hi _ _ _ _ highRun viewValue (.view actual element)
        (types_lowerBound lo _ _ _ _ lowRun viewValue (.view actual element) viewTyped)
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have operation := readonlySlice_resultTy (le := lowerEnv env.mod env.vars results)
          retainedView retainedLow highTyped origin
        have recorded := emitDef_recorded current operation
        rw [emitted] at recorded
        exact recorded.2.2.1
  | conv kind target expr origin =>
    obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, shape, range⟩ := tyExpr_conversion_child source
    subst ty
    subst target
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨child, middle, childRun, tailRun⟩ := bind_eq.mp lowering
    have middleLive := (DeadRun.bind (dead_intTyOf child) fun _ => dead_emitDef _).live_before tailRun live
    have typed := lowerExpr_generated_typed expr childSource childRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation : (Op.conv kind src dst child (some origin)).resultTy
          (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data (.int dst)) := by
        cases kind <;> simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
          range, pure, Except.pure, bind, Except.bind]
      simp only [lowerExpr, bind_run, childRun, intTyOf_recorded typed] at run
      have recorded := emitDef_recorded current operation
      rw [run] at recorded
      exact recorded.2.2.1
  | cmp op left right =>
    obtain ⟨leftTy, rightTy, leftFinish, rightFinish, leftSource, rightSource, shape, scalar⟩ :=
      tyExpr_comparison_children source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨leftValue, leftAfter, leftRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨rightValue, middle, rightRun, tailRun⟩ := bind_eq.mp lowering
    have tailDead : DeadRun (do
        match (← valTy leftValue) with
        | .data (.int t) => emitDef (.cmp op t leftValue rightValue)
        | _ => emitDef (.boolCmp op leftValue rightValue)) := by
      exact DeadRun.bind (dead_valTy leftValue) fun t => by
        cases t with
        | data t => cases t <;> exact dead_emitDef _
        | view _ _ => exact dead_emitDef _
    have middleLive := tailDead.live_before tailRun live
    have leftGenerated := generated.lowerExpr left leftRun
    have rightTyped := lowerExpr_generated_typed right rightSource rightRun middleLive
    have leftLive := (dead_lowerExpr right).live_before rightRun middleLive
    have leftTyped := lowerExpr_generated_typed left leftSource leftRun leftLive
    have retained := types_lowerExpr right _ _ _ _ rightRun leftValue (.data leftTy) leftTyped
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      rcases scalar with ⟨intTy, rfl, rfl⟩ | ⟨rfl, rfl, comparable⟩
      · have operation : (Op.cmp op intTy leftValue rightValue).resultTy
            (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data .bool) := by
          simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, retained, rightTyped,
            pure, Except.pure, bind, Except.bind]
        simp only [lowerExpr, bind_run, leftRun, rightRun, valTy_of_recorded retained] at run
        have recorded := emitDef_recorded current operation
        rw [run] at recorded
        exact recorded.2.2.1
      · have operation : (Op.boolCmp op leftValue rightValue).resultTy
            (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data .bool) := by
          rcases comparable with rfl | rfl <;>
            simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, retained, rightTyped,
              pure, Except.pure, bind, Except.bind]
        simp only [lowerExpr, bind_run, leftRun, rightRun, valTy_of_recorded retained] at run
        have recorded := emitDef_recorded current operation
        rw [run] at recorded
        exact recorded.2.2.1
  | pop owner origin =>
    obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
    simp only [lowerExpr] at run
    obtain ⟨address, middle, ownerRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.pop address (some origin))).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation : (Op.pop address (some origin)).resultTy
          (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data ty) := by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed, element,
          pure, Except.pure, bind, Except.bind]
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | push owner expr origin =>
    obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
      ownerSource, ownerElement, childSource, shape⟩ := tyExpr_push_children source
    subst ty
    simp only [lowerExpr] at run
    obtain ⟨address, ownerAfter, ownerRun, run⟩ := bind_eq.mp run
    obtain ⟨value, middle, childRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.push address value origin)).live_before emitted live
    have ownerGenerated := generated.lowerPlace owner ownerRun
    have childTyped := lowerExpr_generated_typed expr childSource childRun middleLive
    have ownerLive := (dead_lowerExpr expr).live_before childRun middleLive
    obtain ⟨mu, ownerTyped⟩ := lowerPlace_generated_typed owner ownerSource ownerRun ownerLive
    have retained := types_lowerExpr expr _ _ _ _ childRun address (.data (.ref mu info.ty)) ownerTyped
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation : (Op.push address value origin).resultTy
          (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data (.ref .mutable element)) := by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, retained, childTyped,
          ownerElement, pure, Except.pure, bind, Except.bind]
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | arrLit arrayTy exprs =>
    obtain ⟨shape, element, childStart, childFinish, arrayShape, count, childrenSource⟩ := tyExpr_arrayLiteral_children source
    subst ty
    have structSource := tyExprsAs_structExprs childrenSource
    simp only [lowerExpr] at run
    obtain ⟨values, middle, childrenRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.arrLit arrayTy values)).live_before emitted live
    have typed := lowerExprs_generated_typed exprs structSource childrenRun middleLive
    have length : exprs.length = values.length := by simpa only [List.length_replicate] using typed.length_eq
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation := arrayLiteral_resultTy (le := lowerEnv env.mod env.vars results)
        arrayShape (by simpa only [← length] using count) typed.replicate
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | structLit structTy exprs =>
    obtain ⟨shape, descriptor, definitionFinish, childStart, childFinish, definition, childrenSource⟩ :=
      tyExpr_structLiteral_children source
    subst ty
    simp only [lowerExpr] at run
    obtain ⟨values, middle, childrenRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.structLit structTy values)).live_before emitted live
    have typed := lowerExprs_generated_typed exprs childrenSource childrenRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation := structLiteral_resultTy (vars := env.vars) (results := results) definition typed
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | fill arrayTy expr =>
    obtain ⟨shape, element, size, childStart, childFinish, arrayShape, childSource⟩ := tyExpr_fill_child source
    subst ty
    subst arrayTy
    simp only [lowerExpr] at run
    obtain ⟨value, middle, childRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.arrFill (.arr element size) value)).live_before emitted live
    have typed := lowerExpr_generated_typed expr childSource childRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have operation : (Op.arrFill (.arr element size) value).resultTy
          (tyEnv (lowerEnv env.mod env.vars results) middle) = .ok (.data (.arr element size)) := by
        simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
      have recorded := emitDef_recorded current operation
      rw [emitted] at recorded
      exact recorded.2.2.1
  | call context args origin =>
    obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextRow, calleeRow,
      sameLength, argsSource, resultSource⟩ := tyExpr_call_tables source
    have signature := lower_context_sigs_at env.vars results contextRow calleeRow
    simp only [lowerExpr] at run
    obtain ⟨arguments, middle, argsRun, run⟩ := bind_eq.mp run
    obtain ⟨result, emitted, emitRun, tailRun⟩ := bind_eq.mp run
    rw [call_result_tail_run] at tailRun
    by_cases returns : (lowerEnv env.mod env.vars results).mod.noReturn context = true
    · simp only [returns, ite_true] at tailRun
      cases current : emitted.cur with
      | none =>
        rw [emitTerm_none _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        simp [current] at live
      | some block =>
        rw [emitTerm_run _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        contradiction
    · simp only [returns] at tailRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj tailRun
      have middleLive := (dead_emitDef (.call context arguments (some origin))).live_before emitRun live
      have argumentsTyped := lowerArgs_generated_typed args sameLength argsSource argsRun middleLive
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have operation := call_resultTy_of_passable signature argumentsTyped resultSource origin
        have recorded := emitDef_recorded current operation
        rw [emitRun] at recorded
        exact recorded.2.2.1
  | and a b =>
    have typed := lowerExpr_and_source_result_typed source results before
    rw [run] at typed
    exact typed live
  | or a b =>
    have typed := lowerExpr_or_source_result_typed source results before
    rw [run] at typed
    exact typed live
  | blockE body =>
    exact lowerBlock_generated_typed body source run live
  | ifE condition thenBody elseBody =>
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
      obtain ⟨conditionValue, middle, conditionRun, run⟩ := bind_eq.mp run
      cases current : middle.cur with
      | none =>
        rw [whenLive_none _ _ _ current] at run
        obtain ⟨_, rfl⟩ := Prod.mk.inj run
        simp [current] at live
      | some block =>
        rw [whenLive_some _ _ _ current] at run
        obtain ⟨arms, forked, forkRun, run⟩ := bind_eq.mp run
        obtain ⟨_, thenStart, thenStartRun, run⟩ := bind_eq.mp run
        obtain ⟨thenValue, thenAfter, thenRun, run⟩ := bind_eq.mp run
        obtain ⟨thenEnd, thenClosed, thenEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at thenEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj thenEndRun
        obtain ⟨_, elseStart, elseStartRun, run⟩ := bind_eq.mp run
        obtain ⟨elseValue, elseAfter, elseRun, run⟩ := bind_eq.mp run
        obtain ⟨elseEnd, elseClosed, elseEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at elseEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj elseEndRun
        have middleGenerated := generated.lowerExpr condition conditionRun
        have forkGenerated := middleGenerated.fork conditionValue forkRun
        have ids := fork_ids forkRun
        have thenBound : arms.1 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
        have elseBound : arms.2 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.add_lt_add_left (by decide : 1 < 2) _
        have thenGenerated := forkGenerated.setCur (some arms.1)
          (by intro target same; cases same; exact thenBound) thenStartRun
        have thenAfterGenerated := thenGenerated.lowerBlock none [] true thenBody trivial thenRun
        have elseTargetBound : arms.2 < thenAfter.blocks.size := by
          rw [← (generated_setCur_sizes thenStartRun).1] at elseBound
          exact Nat.lt_of_lt_of_le elseBound (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).ext.1
        have elseGenerated := thenAfterGenerated.setCur (some arms.2)
          (by intro target same; cases same; exact elseTargetBound) elseStartRun
        have thenTyped : thenAfter.cur.isSome = true → elseAfter.vals[thenValue]? = some (some (.data thenTy)) := by
          intro branchLive
          have typed := lowerBlock_generated_typed thenBody thenSource thenRun branchLive
          have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data thenTy) typed
          exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data thenTy) retained
        have elseTyped : elseAfter.cur.isSome = true → elseAfter.vals[elseValue]? = some (some (.data thenTy)) := by
          intro branchLive
          exact lowerBlock_generated_typed elseBody elseSource elseRun branchLive
        have joined := joinValue_typed (le := lowerEnv env.mod env.vars results) thenTyped elseTyped
        rw [run] at joined
        exact joined live
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenTy) elseFinish = .ok (ty, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem lowerPlace_generated_typed (p : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env p start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace p (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  cases p with
  | var x | global g =>
    exact lowerPlace_static_live_typed (by trivial) source run live
  | field owner index =>
    have children := source
    simp only [Core.tyPlace] at children
    obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have lowered := lowerPlace_field_typed_of_owner ownerSource source ownerRun typed current
      rw [run] at lowered
      obtain ⟨resultMu, _, typed⟩ := lowered
      exact ⟨resultMu, typed⟩
  | deref e =>
    cases special : Core.sliceRefTy env e with
    | none =>
      obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
      exact ⟨mu, lowerExpr_generated_typed e childSource run live⟩
    | some target =>
      cases e with
      | read p =>
        cases p with
        | var x => exact lowerPlace_static_live_typed (by trivial) source run live
        | _ => simp [Core.sliceRefTy] at special
      | _ => simp [Core.sliceRefTy] at special
  | elem v i origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, intTy, viewSource, indexSource⟩ := tyPlace_elem_children source
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨view, viewAfter, viewRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨index, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked view index (some origin))).live_before emitted live
    have viewGenerated := generated.lowerView v viewRun
    have indexTyped := lowerExpr_generated_typed i indexSource indexRun indexLive
    have viewLive := (dead_lowerExpr i).live_before indexRun indexLive
    obtain ⟨mu, viewTyped⟩ := lowerView_generated_typed v viewSource viewRun viewLive
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block =>
      have lowered := lowerPlace_elem_typed_of_children (origin := origin) viewRun viewTyped indexRun indexTyped current
      rw [run] at lowered
      exact ⟨mu, lowered.2⟩

theorem lowerView_generated_typed (v : View)
    {env : Core.TEnv} {pair : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env v start = .ok (pair, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView v (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : ∃ mu, after.vals[value]? = some (some (.view mu pair.1)) := by
  cases v with
  | of p =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨info, next, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    have lowering := run
    simp only [lowerView] at lowering
    obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef _).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_generated_typed p placeSource placeRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have lowered := lowerView_of_typed_of_place placeSource source placeRun typed current
      rw [run] at lowered
      obtain ⟨resultMu, _, typed⟩ := lowered
      exact ⟨resultMu, typed⟩
  | val e =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨childTy, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp children
    cases childTy with
    | slice mu element =>
      have lowering := run
      simp only [lowerView] at lowering
      obtain ⟨slice, middle, childRun, emitted⟩ := bind_eq.mp lowering
      have middleLive := (dead_emitDef (.sliceView slice)).live_before emitted live
      have typed := lowerExpr_generated_typed e childSource childRun middleLive
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have lowered := lowerView_val_typed_of_expr childSource source childRun typed current
        rw [run] at lowered
        exact ⟨mu, lowered.2⟩
    | _ => exact (rej_ok _ _ _ _).mp tail |>.elim

theorem lowerBound_generated_typed (bound : Bound)
    {env : Core.TEnv} {start finish : Nat}
    (source : Core.tyBound env bound start = .ok ((), finish))
    {results : List Ty} {before after : LS} {value : Bnd}
    (run : lowerBound bound (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : BoundTyped after value := by
  cases bound with
  | omitted =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    trivial
  | expr expr | fromEnd expr =>
    obtain ⟨intTy, childFinish, childSource⟩ := tyBound_child source
    simp only [lowerBound] at run
    obtain ⟨result, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨intTy, lowerExpr_generated_typed expr childSource childRun live⟩

theorem lowerExprs_generated_typed (exprs : List Expr)
    {env : Core.TEnv} {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    {results : List Ty} {before after : LS} {values : List ValueId}
    (run : lowerExprs exprs (lowerEnv env.mod env.vars results) before = (values, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : TypedValues after types values := by
  cases exprs with
  | nil =>
    cases types with
    | nil =>
      obtain ⟨rfl, rfl⟩ := pure_eq.mp run
      exact .nil
    | cons _ _ => exact (rej_ok _ _ _ _).mp source |>.elim
  | cons expr rest =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons expected types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨ty, next, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases equal : (ty == expected) = true
      · simp only [equal, ite_true] at source
        have same := eq_of_beq equal
        subst ty
        simp only [lowerExprs] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        have middleGenerated := generated.lowerExpr expr childRun
        have restTyped := lowerExprs_generated_typed rest source restRun live
        have middleLive := (dead_lowerExprs rest).live_before restRun live
        have childTyped := lowerExpr_generated_typed expr childSource childRun middleLive
        have retained := types_lowerExprs rest _ _ _ _ restRun value (.data expected) childTyped
        exact .cons retained restTyped
      · simp [equal, chk] at source

theorem lowerArgs_generated_typed (args : List Arg)
    {env : Core.TEnv} {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    {results : List Ty} {before after : LS} {values : List ValueId}
    (run : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    PassableValues after (params.map (fun param => tyOfVar callee param.var)) values := by
  cases args with
  | nil =>
    cases params with
    | nil =>
      obtain ⟨rfl, rfl⟩ := pure_eq.mp run
      exact .nil
    | cons _ _ => simp at sameLength
  | cons arg args =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      cases arg with
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        simp only [lowerArgs] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        have middleGenerated := generated.lowerArg (.byRef mu place) childRun
        have restTyped := lowerArgs_generated_typed args (by simpa using sameLength)
          restSource restRun live
        have middleLive := (dead_lowerArgs args).live_before restRun live
        have lowering := childRun
        simp only [lowerArg] at lowering
        obtain ⟨address, placeAfter, placeRun, freezeRun⟩ := bind_eq.mp lowering
        have placeLive := (dead_borrowTo mu address).live_before freezeRun middleLive
        have childTyped : middle.vals[value]? = some (some (.data (.ref mu info.ty))) := by
          cases mu with
          | readOnly =>
            obtain ⟨actual, placeTyped⟩ := lowerPlace_generated_typed place placeSource placeRun placeLive
            cases current : placeAfter.cur with
            | none => simp [current] at placeLive
            | some block =>
              have permission : actual.atLeast .readOnly = true := by cases actual <;> rfl
              have typed := lowerArg_byRef_typed_of_place placeRun placeTyped permission current
              rw [childRun] at typed
              exact typed
          | mutable =>
            have typed := lowerPlace_generated_writable_typed place placeSource (writable rfl) placeRun placeLive
            cases current : placeAfter.cur with
            | none => simp [current] at placeLive
            | some block =>
              have frozen := lowerArg_byRef_typed_of_place (requested := .mutable) placeRun typed (by rfl) current
              rw [childRun] at frozen
              exact frozen
        have retained := types_lowerArgs args _ _ _ _ restRun value (.data (.ref mu info.ty)) childTyped
        exact .cons ⟨.ref mu info.ty, retained, by simpa [tyOfVar, row] using permission⟩ restTyped
      | byVal expr =>
        obtain ⟨localVar, argTy, childStart, childFinish, restStart,
          row, childSource, permission, restSource⟩ := tyArgs_byVal_head source
        simp only [lowerArgs, lowerArg] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        have middleGenerated := generated.lowerExpr expr childRun
        have restTyped := lowerArgs_generated_typed args (by simpa using sameLength)
          restSource restRun live
        have middleLive := (dead_lowerArgs args).live_before restRun live
        have childTyped := lowerExpr_generated_typed expr childSource childRun middleLive
        have retained := types_lowerArgs args _ _ _ _ restRun value (.data argTy) childTyped
        exact .cons ⟨argTy, retained, by simpa [tyOfVar, row] using permission⟩ restTyped

theorem lowerBlock_generated_typed (body : Core.Block)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : after.vals[value]? = some (some (.data ty)) := by
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
      obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
      obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
      obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
      obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
      obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
      subst after
      subst value
      obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
      have poppedLive := dead_popScope.live_before popRun live
      have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
      have enteredGenerated := generated.emitEffect (.enter scope) enterRun
      have pushedGenerated := generated_pushScope enteredGenerated pushRun
      have initializedGenerated := pushedGenerated.initSlots [] initRun
      have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
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
            rw [← sameEnv] at valueRun
            exact lowerExpr_generated_typed e source valueRun valueLive
      have retained := types_emitEffect (.leave scope) _ _ _ _ leaveRun result (.data ty) resultTyped
      exact types_popScope _ _ _ _ popRun result (.data ty) retained

theorem lowerPlace_generated_writable_typed (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    after.vals[value]? = some (some (.data (.ref .mutable info.ty))) := by
  cases place with
  | var index =>
    have initial := (dead_lowerPlace (.var index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerPlace_var_exact source results before current
      rw [run] at typed
      simpa only [referenceType, writable, ite_true] using typed.2
  | global index =>
    have initial := (dead_lowerPlace (.global index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerPlace_global_exact source env.vars results before current
      rw [run] at typed
      simpa only [referenceType, writable, ite_true] using typed.2
  | field owner index =>
    obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, _, _, _⟩ :=
      tyPlace_field_mutable_binding source writable
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    obtain ⟨actual, ownerTyped⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have typed := lowerPlace_field_mutable_typed_of_owner source writable ownerSource ownerRun ownerTyped current
      rw [run] at typed
      exact typed.2
  | deref expr =>
    exact lowerPlace_deref_writable_typed_of_child source writable run live
      (fun childFinish childSource => lowerExpr_generated_typed expr childSource run live)
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, intTy, viewSource, indexSource⟩ :=
      tyPlace_elem_writable_children source writable
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨viewValue, viewAfter, viewRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨indexValue, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked viewValue indexValue (some origin))).live_before emitted live
    have viewGenerated := generated.lowerView view viewRun
    have indexTyped := lowerExpr_generated_typed index indexSource indexRun indexLive
    have viewLive := (dead_lowerExpr index).live_before indexRun indexLive
    have viewTyped := lowerView_generated_writable_typed view viewSource viewRun viewLive
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block =>
      have typed := lowerPlace_elem_typed_of_children (origin := origin) viewRun viewTyped indexRun indexTyped current
      rw [run] at typed
      exact typed.2

theorem lowerView_generated_writable_typed (view : View)
    {env : Core.TEnv} {element : Ty} {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, true), finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    after.vals[value]? = some (some (.view .mutable element)) := by
  cases view with
  | val expr =>
    exact lowerView_val_writable_typed_of_child source run live
      (fun childFinish childState childValue childSource childRun childLive =>
        lowerExpr_generated_typed expr childSource childRun childLive)
  | of place =>
    obtain ⟨info, placeFinish, placeSource, container, writable⟩ := tyView_of_writable_place source
    have lowering := run
    simp only [lowerView] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef _).live_before emitted live
    obtain ⟨actual, ownerTyped⟩ := lowerPlace_generated_typed place placeSource ownerRun middleLive
    have evidence := lowerPlace_generated_contents place placeSource container writable ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have typed := lowerView_of_writable_typed_of_place placeSource source ownerRun ownerTyped evidence.forget current
      rw [run] at typed
      exact typed.2


theorem lowerExpr_generated_contents (expr : Expr)
    {env : Core.TEnv} {target : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (.ref .mutable target, finish))
    (container : ContentsTarget target)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  have form := tyExpr_mutable_reference_form source
  cases expr with
  | read place =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.load address)).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have evidence := lowerExpr_read_fresh_contents source placeRun
        (fun info childFinish childSource => lowerPlace_generated_typed place childSource placeRun middleLive)
        middleGenerated.dense middleGenerated.live current run
      exact evidence.weaken (advB_lowerPlace place _ _ _ _ placeRun).vals
  | ref mu place =>
    obtain ⟨info, placeFinish, placeSource, shape, writable⟩ := tyExpr_ref_place source
    cases mu with
    | readOnly => cases shape
    | mutable =>
      obtain ⟨actualInfo, actualFinish, actualSource, referent, contents⟩ :=
        source_mutable_reference_contents source container
      rw [placeSource] at actualSource
      cases Except.ok.inj actualSource
      have ownerContainer : ContentsTarget info.ty := by rw [referent]; exact container
      have lowering := run
      simp only [lowerExpr] at lowering
      obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp lowering
      have middleLive := (dead_borrowTo .mutable owner).live_before borrowed live
      have middleGenerated := generated.lowerPlace place placeRun
      have authority : info.referenceWritable env.mod.profile = true := by
        cases allowed : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
      have typed := lowerPlace_generated_writable_typed place placeSource authority placeRun middleLive
      have evidence := lowerPlace_generated_contents place placeSource ownerContainer contents placeRun middleLive
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block => exact evidence.borrowTo_mutable typed middleGenerated.dense middleGenerated.live current borrowed
  | pop owner origin =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.pop address (some origin))).live_before emitted live
    have middleGenerated := generated.lowerPlace owner ownerRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have evidence := lowerExpr_pop_fresh_contents source ownerRun
        (fun info childStart childFinish childSource => lowerPlace_generated_typed owner childSource ownerRun middleLive)
        middleGenerated.dense middleGenerated.live current run
      exact evidence.weaken (advB_lowerPlace owner _ _ _ _ ownerRun).vals
  | push owner child origin =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, ownerAfter, ownerRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨childValue, middle, childRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.push address childValue origin)).live_before emitted live
    have ownerLive := (dead_lowerExpr child).live_before childRun middleLive
    have ownerGenerated := generated.lowerPlace owner ownerRun
    have middleGenerated := ownerGenerated.lowerExpr child childRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have evidence := lowerExpr_push_fresh_contents source ownerRun childRun
        (fun info childStart childFinish childSource => by
          obtain ⟨mu, typed⟩ := lowerPlace_generated_typed owner childSource ownerRun ownerLive
          exact ⟨mu, types_lowerExpr child _ _ _ _ childRun address _ typed⟩)
        (fun ty childStart childFinish childSource => lowerExpr_generated_typed child childSource childRun middleLive)
        middleGenerated.dense middleGenerated.live current run
      exact evidence.weaken (Nat.le_trans (advB_lowerPlace owner _ _ _ _ ownerRun).vals
        (advB_lowerExpr child _ _ _ _ childRun).vals)
  | call context args origin =>
    obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextRow, calleeRow,
      sameLength, argsSource, resultSource⟩ := tyExpr_call_tables source
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨arguments, middle, argsRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨emittedValue, emitted, emitRun, tailRun⟩ := bind_eq.mp lowering
    rw [call_result_tail_run] at tailRun
    by_cases returns : (lowerEnv env.mod env.vars results).mod.noReturn context = true
    · simp only [returns, ite_true] at tailRun
      cases current : emitted.cur with
      | none =>
        rw [emitTerm_none _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        simp [current] at live
      | some block =>
        rw [emitTerm_run _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        contradiction
    · simp only [returns] at tailRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj tailRun
      have middleLive := (dead_emitDef (.call context arguments (some origin))).live_before emitRun live
      have middleGenerated := generated.lowerArgs args argsRun
      have argumentsTyped := lowerArgs_generated_typed args sameLength argsSource argsRun middleLive
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have evidence := lowerExpr_call_fresh_contents_of_args source argsRun (by
          intro actualCtx actualCallee actualContextRow actualCalleeRow
          rw [contextRow] at actualContextRow
          cases Option.some.inj actualContextRow
          rw [calleeRow] at actualCalleeRow
          cases Option.some.inj actualCalleeRow
          exact ⟨callee.params.toList.map (fun param => tyOfVar callee param.var), lower_context_sigs_at env.vars results contextRow calleeRow,
            argumentsTyped⟩) middleGenerated.dense middleGenerated.live current emitRun run
        exact evidence.weaken (advB_lowerArgs args _ _ _ _ argsRun).vals
  | blockE body => exact lowerBlock_generated_contents body source container run live
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨thenTy, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨elseTy, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (thenTy == elseTy) = true
    · simp only [equal, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      change Ty.ref .mutable target = thenTy at shape
      have typesEqual : thenTy = elseTy := eq_of_beq equal
      subst elseTy
      subst thenTy
      simp only [lowerExpr] at run
      obtain ⟨conditionValue, middle, conditionRun, run⟩ := bind_eq.mp run
      cases current : middle.cur with
      | none =>
        rw [whenLive_none _ _ _ current] at run
        obtain ⟨_, rfl⟩ := Prod.mk.inj run
        simp [current] at live
      | some block =>
        rw [whenLive_some _ _ _ current] at run
        obtain ⟨arms, forked, forkRun, run⟩ := bind_eq.mp run
        obtain ⟨_, thenStart, thenStartRun, run⟩ := bind_eq.mp run
        obtain ⟨thenValue, thenAfter, thenRun, run⟩ := bind_eq.mp run
        obtain ⟨thenEnd, thenClosed, thenEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at thenEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj thenEndRun
        obtain ⟨_, elseStart, elseStartRun, run⟩ := bind_eq.mp run
        obtain ⟨elseValue, elseAfter, elseRun, run⟩ := bind_eq.mp run
        obtain ⟨elseEnd, elseClosed, elseEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at elseEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj elseEndRun
        have middleGenerated := generated.lowerExpr condition conditionRun
        have forkGenerated := middleGenerated.fork conditionValue forkRun
        have ids := fork_ids forkRun
        have thenBound : arms.1 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
        have elseBound : arms.2 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.add_lt_add_left (by decide : 1 < 2) _
        have thenGenerated := forkGenerated.setCur (some arms.1)
          (by intro target same; cases same; exact thenBound) thenStartRun
        have thenAfterGenerated := thenGenerated.lowerBlock none [] true thenBody trivial thenRun
        have elseTargetBound : arms.2 < thenAfter.blocks.size := by
          rw [← (generated_setCur_sizes thenStartRun).1] at elseBound
          exact Nat.lt_of_lt_of_le elseBound (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).ext.1
        have elseGenerated := thenAfterGenerated.setCur (some arms.2)
          (by intro target same; cases same; exact elseTargetBound) elseStartRun
        have thenTyped : thenAfter.cur.isSome = true → elseAfter.vals[thenValue]? = some (some (.data (.ref .mutable target))) := by
          intro branchLive
          have typed := lowerBlock_generated_typed thenBody thenSource thenRun branchLive
          have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data (.ref .mutable target)) typed
          exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data (.ref .mutable target)) retained
        have elseTyped : elseAfter.cur.isSome = true → elseAfter.vals[elseValue]? = some (some (.data (.ref .mutable target))) := by
          intro branchLive
          exact lowerBlock_generated_typed elseBody elseSource elseRun branchLive
        have elseAfterGenerated := elseGenerated.lowerBlock none [] true elseBody trivial elseRun
        have beforeThen : before.vals.size ≤ thenStart.vals.size := by
          have a := (advB_lowerExpr condition _ _ _ _ conditionRun).vals
          have b := (advB_fork conditionValue _ _ _ _ forkRun).vals
          have c := (generated_setCur_sizes thenStartRun).2
          omega
        have beforeElse : before.vals.size ≤ elseStart.vals.size := by
          have a := (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).vals
          have b := (generated_setCur_sizes elseStartRun).2
          omega
        have beforeJoin : before.vals.size ≤ elseAfter.vals.size := Nat.le_trans beforeElse
          (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).vals
        have thenEvidence : thenAfter.cur.isSome = true →
            FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter thenValue := by
          intro branchLive
          have evidence := (lowerBlock_generated_contents thenBody thenSource container thenRun branchLive).weaken beforeThen
          have moved := evidence.setCur elseStartRun
          exact moved.of_framed_run (loop := none) elseRun (dense_lowerBlock none [] true elseBody)
            (advB_lowerBlock none [] true elseBody) (types_lowerBlock none [] true elseBody)
            (generatedTargetFrame_lowerBlock none [] true elseBody) elseGenerated.dense elseGenerated.live trivial
        have elseEvidence : elseAfter.cur.isSome = true →
            FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter elseValue := by
          intro branchLive
          exact (lowerBlock_generated_contents elseBody elseSource container elseRun branchLive).weaken beforeElse
        have thenBound : ∀ endpoint, thenAfter.cur = some endpoint → endpoint < elseAfter.blocks.size := by
          intro endpoint row
          have bounded := thenAfterGenerated.live endpoint row
          apply Nat.lt_of_lt_of_le bounded
          exact Nat.le_trans (Nat.le_of_eq (generated_setCur_sizes elseStartRun).1.symm)
            (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).ext.1
        have joined := joinValue_freshContents elseAfterGenerated.dense elseAfterGenerated.live
          elseAfterGenerated.targets thenBound elseAfterGenerated.live thenTyped elseTyped
          (by intro intTy unequal; cases unequal) beforeJoin thenEvidence elseEvidence
        rw [run] at joined
        exact (joined live).1
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenTy) elseFinish = .ok (.ref .mutable target, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim
  | _ => simp only [MutableReferenceExpression] at form


theorem lowerPlace_generated_contents (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (container : ContentsTarget info.ty) (contents : info.contentsWritable = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases place with
  | var index =>
    have initial := (dead_lowerPlace (.var index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block => exact lowerPlace_var_fresh_contents source generated.dense generated.live current run
  | global index =>
    have initial := (dead_lowerPlace (.global index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block => exact lowerPlace_global_fresh_contents source generated.dense generated.live current run
  | field owner index =>
    obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, fieldSource, ownerContents, mutable⟩ :=
      tyPlace_field_contents_children source contents
    obtain ⟨id, fields, descriptor, shape, descriptorRow, _, fieldRow⟩ := structField_descriptor fieldSource
    have ownerContainer : ContentsTarget ownerInfo.ty := by rw [shape]; trivial
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    have middleGenerated := generated.lowerPlace owner ownerRun
    obtain ⟨actual, ownerTyped⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive
    have evidence := lowerPlace_generated_contents owner ownerSource ownerContainer ownerContents ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact lowerPlace_field_fresh_contents_of_owner source contents ownerSource ownerRun ownerTyped
        evidence middleGenerated.dense middleGenerated.live current run
  | deref expr =>
    apply lowerPlace_deref_fresh_contents_of_child source container contents run
    intro childFinish childSource childRun
    exact lowerExpr_generated_contents expr childSource container childRun live
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, intTy, viewSource, indexSource⟩ :=
      tyPlace_elem_contents_children source contents
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨viewValue, viewAfter, viewRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨indexValue, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked viewValue indexValue (some origin))).live_before emitted live
    have viewLive := (dead_lowerExpr index).live_before indexRun indexLive
    have viewGenerated := generated.lowerView view viewRun
    have evidence := lowerView_generated_contents view viewSource viewRun viewLive
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block =>
      exact lowerPlace_elem_fresh_contents_of_children viewRun indexRun evidence
        viewGenerated.dense viewGenerated.live current run

theorem lowerView_generated_contents (view : View)
    {env : Core.TEnv} {element : Ty} {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, true), finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases view with
  | val expr =>
    obtain ⟨childFinish, childSource⟩ := tyView_val_writable_child source
    have lowering := run
    simp only [lowerView] at lowering
    obtain ⟨childValue, middle, childRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.sliceView childValue)).live_before emitted live
    have middleGenerated := generated.lowerExpr expr childRun
    have typed := lowerExpr_generated_typed expr childSource childRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have evidence := lowerView_val_fresh_contents_of_child childRun typed middleGenerated.dense
        middleGenerated.live current run
      exact evidence.weaken (advB_lowerExpr expr _ _ _ _ childRun).vals
  | of place =>
    obtain ⟨info, placeFinish, placeSource, container, contents⟩ := tyView_of_writable_place source
    have lowering := run
    simp only [lowerView] at lowering
    obtain ⟨ownerValue, middle, placeRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef _).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    have evidence := lowerPlace_generated_contents place placeSource container contents placeRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact lowerView_of_fresh_contents_of_place placeRun evidence middleGenerated.dense
        middleGenerated.live current run


theorem lowerBlock_generated_contents (body : Core.Block)
    {env : Core.TEnv} {target : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (.ref .mutable target, finish))
    (container : ContentsTarget target)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by generated_builder) : FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
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
      obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
      obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
      obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
      obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
      obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
      subst after
      subst value
      obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
      have poppedLive := dead_popScope.live_before popRun live
      have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
      have enteredGenerated := generated.emitEffect (.enter scope) enterRun
      have pushedGenerated := generated_pushScope enteredGenerated pushRun
      have initializedGenerated := pushedGenerated.initSlots [] initRun
      have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
      have resultEvidence : FreshContentsEvidence (lowerEnv env.mod env.vars results)
          statementsAfter.vals.size valueAfter result := by
        cases expression with
        | none =>
          have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
          cases shape
        | some expr =>
          simp only [lowerBlockValue] at valueRun
          rw [← sameEnv] at valueRun
          have evidence := lowerExpr_generated_contents expr source container valueRun valueLive
          rw [sameEnv] at evidence
          exact evidence
      have valueGenerated := statementsGenerated.lowerBlockValue true expression valueRun
      have retained := resultEvidence.of_framed_run (loop := none) leaveRun (dense_emitEffect _)
        (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
        valueGenerated.dense valueGenerated.live trivial
      rw [popScope_run] at popRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
      have growth : before.vals.size ≤ statementsAfter.vals.size := by
        have one := (advB_emitEffect (.enter scope) _ _ _ _ enterRun).vals
        have two : entered.vals.size ≤ pushed.vals.size := by
          rw [pushScope_run] at pushRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
          exact Nat.le_refl _
        have three := (advB_initSlots [] _ _ _ _ initRun).vals
        have four := (advB_lowerStmts none statements _ _ _ _ statementsRun).vals
        omega
      exact retained.weaken growth




end

#print axioms lowerExpr_generated_typed
#print axioms lowerPlace_generated_typed
#print axioms lowerView_generated_typed
#print axioms lowerPlace_generated_writable_typed
#print axioms lowerView_generated_writable_typed
#print axioms lowerPlace_generated_contents
#print axioms lowerView_generated_contents
#print axioms lowerExpr_generated_contents

end Goose.Lower.Validation
