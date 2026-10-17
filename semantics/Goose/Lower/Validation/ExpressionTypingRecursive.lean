import Goose.Lower.Validation.ExpressionTypingMutableElemOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

mutual

def RecursiveExpression : Expr → Prop
  | .read p | .ref .readOnly p => RecursivePlace p
  | .ref .mutable (.field owner _) => RecursivePlace owner
  | .ref .mutable (.deref expr) => RecursiveExpression expr
  | .ref .mutable (.elem (.val expr) index _) => RecursiveExpression expr ∧ RecursiveExpression index
  | .un _ e _ | .not e | .conv _ _ e _ => RecursiveExpression e
  | .bin _ a b _ | .cmp _ a b => RecursiveExpression a ∧ RecursiveExpression b
  | .push owner expr _ => RecursivePlace owner ∧ RecursiveExpression expr
  | .pop owner _ => RecursivePlace owner
  | .len v => RecursiveView v
  | .slice .readOnly view lo hi _ => RecursiveView view ∧ RecursiveBound lo ∧ RecursiveBound hi
  | .slice .mutable (.val expr) lo hi _ => RecursiveExpression expr ∧ RecursiveBound lo ∧ RecursiveBound hi
  | .call _ args _ => RecursiveArguments args
  | .arrLit _ exprs | .structLit _ exprs => RecursiveExpressions exprs
  | .fill _ expr => RecursiveExpression expr
  | .and _ _ | .or _ _ => True
  | .blockE b => RecursiveBlock b
  | .ifE _ t f => RecursiveBlock t ∧ RecursiveBlock f
  | e => StaticExpression e

def RecursivePlace : Place → Prop
  | .var _ | .global _ => True
  | .field p _ => RecursivePlace p
  | .deref e => RecursiveExpression e
  | .elem v i _ => RecursiveView v ∧ RecursiveExpression i

def RecursiveView : View → Prop
  | .of p => RecursivePlace p
  | .val e => RecursiveExpression e

def RecursiveBound : Bound → Prop
  | .omitted => True
  | .expr expr | .fromEnd expr => RecursiveExpression expr

def RecursiveBlock : Core.Block → Prop
  | .mk _ _ none => True
  | .mk _ _ (some e) => RecursiveExpression e

def RecursiveExpressions : List Expr → Prop
  | [] => True
  | expr :: rest => RecursiveExpression expr ∧ RecursiveExpressions rest

def RecursiveArgument : Arg → Prop
  | .byVal expr => RecursiveExpression expr
  | .byRef .readOnly place => RecursivePlace place
  | .byRef .mutable (.field owner _) => RecursivePlace owner
  | .byRef .mutable (.deref expr) => RecursiveExpression expr
  | .byRef .mutable (.elem (.val expr) index _) => RecursiveExpression expr ∧ RecursiveExpression index
  | .byRef .mutable (.var _) | .byRef .mutable (.global _) => True
  | _ => False

def RecursiveArguments : List Arg → Prop
  | [] => True
  | arg :: args => RecursiveArgument arg ∧ RecursiveArguments args

end

mutual

theorem lowerExpr_recursive_typed (e : Expr) (supported : RecursiveExpression e)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env e start = .ok (ty, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr e (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : after.vals[value]? = some (some (.data ty)) := by
  cases e with
  | lit t n | bool b =>
    have initial := (dead_lowerExpr _).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerExpr_static_typed _ supported source results before current
      rw [run] at typed
      exact typed.2
  | read p =>
    obtain ⟨info, next, placeSource, shape⟩ := tyExpr_read_place source
    subst ty
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, mid, placeRun, emitted⟩ := bind_eq.mp lowering
    have midLive := ((dead_emitDef (.load address)).bind fun value =>
      (dead_recordReadValueRootRecipe value p).bind fun _ => DeadRun.pure value).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_recursive_typed p supported placeSource placeRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have loaded := lowerExpr_read_typed_of_place placeRun typed current
      rw [run] at loaded
      exact loaded.2
  | ref mu p =>
    cases mu with
    | mutable =>
      cases p with
      | field owner index =>
        obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, info, placeFinish,
          ownerSource, _, _, shape, _, _⟩ := tyExpr_ref_mutable_field_binding source
        have lowering := run
        simp only [lowerExpr] at lowering
        obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
        have midLive := (dead_borrowTo .mutable address).live_before frozenRun live
        have placeLowering := placeRun
        simp only [lowerPlace] at placeLowering
        obtain ⟨ownerValue, ownerState, ownerRun, emitted⟩ := bind_eq.mp placeLowering
        have ownerLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted midLive
        obtain ⟨mu, ownerTyped⟩ := lowerPlace_recursive_typed owner supported ownerSource ownerRun ownerLive
        cases current : ownerState.cur with
        | none => simp [current] at ownerLive
        | some block =>
          have typed := lowerPlace_ref_mutable_field_typed_of_owner source ownerSource ownerRun ownerTyped current
          rw [placeRun] at typed
          cases midCurrent : mid.cur with
          | none => simp [midCurrent] at midLive
          | some midBlock =>
            rw [shape] at typed
            have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) (requested := .mutable) typed.2 (by rfl) midCurrent
            rw [frozenRun] at frozen
            simpa only [shape] using frozen.2
      | deref expr =>
        obtain ⟨info, placeFinish, placeSource, shape, permission⟩ := tyExpr_ref_place source
        have writable : info.referenceWritable env.mod.profile = true := by
          cases bound : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
        have lowering := run
        simp only [lowerExpr] at lowering
        obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
        have midLive := (dead_borrowTo .mutable address).live_before frozenRun live
        have typed := lowerPlace_deref_writable_typed_of_child placeSource writable placeRun midLive
          (fun childFinish childSource => lowerExpr_recursive_typed expr supported childSource placeRun midLive)
        cases current : mid.cur with
        | none => simp [current] at midLive
        | some block =>
          have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) (requested := .mutable) typed (by rfl) current
          rw [frozenRun] at frozen
          simpa only [shape] using frozen.2
      | elem view index origin =>
        cases view with
        | of owner => contradiction
        | val expr =>
          obtain ⟨exprSupported, indexSupported⟩ := supported
          obtain ⟨info, placeFinish, placeSource, shape, permission⟩ := tyExpr_ref_place source
          have writable : info.referenceWritable env.mod.profile = true := by
            cases bound : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
          have lowering := run
          simp only [lowerExpr] at lowering
          obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
          have midLive := (dead_borrowTo .mutable address).live_before frozenRun live
          have typed := lowerPlace_elem_val_writable_typed_of_children placeSource writable placeRun midLive
            (fun _ _ _ _ childSource childRun childLive => lowerExpr_recursive_typed expr exprSupported childSource childRun childLive)
            (fun _ _ _ _ _ _ childSource childRun childLive => lowerExpr_recursive_typed index indexSupported childSource childRun childLive)
          cases current : mid.cur with
          | none => simp [current] at midLive
          | some block =>
            have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) (requested := .mutable) typed (by rfl) current
            rw [frozenRun] at frozen
            simpa only [shape] using frozen.2
      | var _ | global _ =>
        have initial := (dead_lowerExpr _).live_before run live
        cases current : before.cur with
        | none => simp [current] at initial
        | some block =>
          have typed := lowerExpr_static_typed _ supported source results before current
          rw [run] at typed
          exact typed.2
    | readOnly =>
      obtain ⟨info, next, placeSource, shape, _⟩ := tyExpr_ref_place source
      subst ty
      have lowering := run
      simp only [lowerExpr] at lowering
      obtain ⟨address, mid, placeRun, frozenRun⟩ := bind_eq.mp lowering
      have midLive := (dead_borrowTo .readOnly address).live_before frozenRun live
      obtain ⟨actual, typed⟩ := lowerPlace_recursive_typed p supported placeSource placeRun midLive
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
    have typed := lowerExpr_recursive_typed e supported childSource childRun midLive
    cases current : mid.cur with
    | none => simp [current] at midLive
    | some block =>
      have lowered := lowerExpr_un_typed_of_child (op := op) (origin := origin) childRun typed signed current
      rw [run] at lowered
      exact lowered.2
  | bin op a b origin =>
    obtain ⟨aStart, aFinish, bStart, bFinish, intTy, aSource, bSource, shape⟩ := tyExpr_bin_children source
    subst ty
    obtain ⟨aSupported, bSupported⟩ := supported
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨av, aState, aRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨bv, mid, bRun, tailRun⟩ := bind_eq.mp lowering
    have midLive := (DeadRun.bind (dead_intTyOf av) fun _ => dead_emitDef _).live_before tailRun live
    have bTyped := lowerExpr_recursive_typed b bSupported bSource bRun midLive
    have aLive := (dead_lowerExpr b).live_before bRun midLive
    have aTyped := lowerExpr_recursive_typed a aSupported aSource aRun aLive
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
    have typed := lowerExpr_recursive_typed e supported childSource childRun midLive
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
    obtain ⟨mu, typed⟩ := lowerView_recursive_typed v supported viewSource viewRun midLive
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
      cases view with
      | of place => contradiction
      | val expr =>
        obtain ⟨element, viewStart, viewFinish, lowFinish, highFinish,
          viewSource, lowSource, highSource, shape⟩ := tyExpr_slice_mutable_children source
        subst ty
        obtain ⟨exprSupported, lowSupported, highSupported⟩ := supported
        simp only [lowerExpr] at run
        obtain ⟨viewValue, viewAfter, viewRun, run⟩ := bind_eq.mp run
        obtain ⟨lowValue, lowAfter, lowRun, run⟩ := bind_eq.mp run
        obtain ⟨highValue, middle, highRun, emitted⟩ := bind_eq.mp run
        have middleLive := (dead_emitDef (.viewSlice .mutable viewValue lowValue highValue (some origin))).live_before emitted live
        have highTyped := lowerBound_recursive_typed hi highSupported highSource highRun middleLive
        have lowLive := (dead_lowerBound hi).live_before highRun middleLive
        have lowTyped := lowerBound_recursive_typed lo lowSupported lowSource lowRun lowLive
        have viewLive := (dead_lowerBound lo).live_before lowRun lowLive
        have viewTyped := lowerView_val_writable_typed_of_child viewSource viewRun viewLive
          (fun childFinish childState childValue childSource childRun childLive =>
            lowerExpr_recursive_typed expr exprSupported childSource childRun childLive)
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
      obtain ⟨viewSupported, lowSupported, highSupported⟩ := supported
      simp only [lowerExpr] at run
      obtain ⟨viewValue, viewAfter, viewRun, run⟩ := bind_eq.mp run
      obtain ⟨lowValue, lowAfter, lowRun, run⟩ := bind_eq.mp run
      obtain ⟨highValue, middle, highRun, emitted⟩ := bind_eq.mp run
      have middleLive := (dead_emitDef (.viewSlice .readOnly viewValue lowValue highValue (some origin))).live_before emitted live
      have highTyped := lowerBound_recursive_typed hi highSupported highSource highRun middleLive
      have lowLive := (dead_lowerBound hi).live_before highRun middleLive
      have lowTyped := lowerBound_recursive_typed lo lowSupported lowSource lowRun lowLive
      have viewLive := (dead_lowerBound lo).live_before lowRun lowLive
      obtain ⟨actual, viewTyped⟩ := lowerView_recursive_typed view viewSupported viewSource viewRun viewLive
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
    have typed := lowerExpr_recursive_typed expr supported childSource childRun middleLive
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
    obtain ⟨leftSupported, rightSupported⟩ := supported
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
    have rightTyped := lowerExpr_recursive_typed right rightSupported rightSource rightRun middleLive
    have leftLive := (dead_lowerExpr right).live_before rightRun middleLive
    have leftTyped := lowerExpr_recursive_typed left leftSupported leftSource leftRun leftLive
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
    obtain ⟨mu, typed⟩ := lowerPlace_recursive_typed owner supported ownerSource ownerRun middleLive
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
    obtain ⟨ownerSupported, childSupported⟩ := supported
    simp only [lowerExpr] at run
    obtain ⟨address, ownerAfter, ownerRun, run⟩ := bind_eq.mp run
    obtain ⟨value, middle, childRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.push address value origin)).live_before emitted live
    have childTyped := lowerExpr_recursive_typed expr childSupported childSource childRun middleLive
    have ownerLive := (dead_lowerExpr expr).live_before childRun middleLive
    obtain ⟨mu, ownerTyped⟩ := lowerPlace_recursive_typed owner ownerSupported ownerSource ownerRun ownerLive
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
    have typed := lowerExprs_recursive_typed exprs supported structSource childrenRun middleLive
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
    have typed := lowerExprs_recursive_typed exprs supported childrenSource childrenRun middleLive
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
    have typed := lowerExpr_recursive_typed expr supported childSource childRun middleLive
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
      have argumentsTyped := lowerArgs_recursive_typed args supported sameLength argsSource argsRun middleLive
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
    exact lowerBlock_recursive_typed body supported source run live
  | ifE condition thenBody elseBody =>
    obtain ⟨thenSupported, elseSupported⟩ := supported
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
        have thenTyped : thenAfter.cur.isSome = true → elseAfter.vals[thenValue]? = some (some (.data thenTy)) := by
          intro branchLive
          have typed := lowerBlock_recursive_typed thenBody thenSupported thenSource thenRun branchLive
          have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data thenTy) typed
          exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data thenTy) retained
        have elseTyped : elseAfter.cur.isSome = true → elseAfter.vals[elseValue]? = some (some (.data thenTy)) := by
          intro branchLive
          exact lowerBlock_recursive_typed elseBody elseSupported elseSource elseRun branchLive
        have joined := joinValue_record_typed (le := lowerEnv env.mod env.vars results)
          (sourceBlockScope thenBody) thenTyped elseTyped
        rw [run] at joined
        exact joined live
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenTy) elseFinish = .ok (ty, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem lowerPlace_recursive_typed (p : Place) (supported : RecursivePlace p)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env p start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace p (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
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
    obtain ⟨mu, typed⟩ := lowerPlace_recursive_typed owner supported ownerSource ownerRun middleLive
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
      exact ⟨mu, lowerExpr_recursive_typed e supported childSource run live⟩
    | some target =>
      cases e with
      | read p =>
        cases p with
        | var x => exact lowerPlace_static_live_typed (by trivial) source run live
        | _ => simp [Core.sliceRefTy] at special
      | _ => simp [Core.sliceRefTy] at special
  | elem v i origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, intTy, viewSource, indexSource⟩ := tyPlace_elem_children source
    obtain ⟨vSupported, iSupported⟩ := supported
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨view, viewAfter, viewRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨index, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked view index (some origin))).live_before emitted live
    have indexTyped := lowerExpr_recursive_typed i iSupported indexSource indexRun indexLive
    have viewLive := (dead_lowerExpr i).live_before indexRun indexLive
    obtain ⟨mu, viewTyped⟩ := lowerView_recursive_typed v vSupported viewSource viewRun viewLive
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block =>
      have lowered := lowerPlace_elem_typed_of_children (origin := origin) viewRun viewTyped indexRun indexTyped current
      rw [run] at lowered
      exact ⟨mu, lowered.2⟩

theorem lowerView_recursive_typed (v : View) (supported : RecursiveView v)
    {env : Core.TEnv} {pair : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env v start = .ok (pair, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView v (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mu, after.vals[value]? = some (some (.view mu pair.1)) := by
  cases v with
  | of p =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨info, next, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    have lowering := run
    simp only [lowerView] at lowering
    obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef _).live_before emitted live
    obtain ⟨mu, typed⟩ := lowerPlace_recursive_typed p supported placeSource placeRun middleLive
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
      have typed := lowerExpr_recursive_typed e supported childSource childRun middleLive
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        have lowered := lowerView_val_typed_of_expr childSource source childRun typed current
        rw [run] at lowered
        exact ⟨mu, lowered.2⟩
    | _ => exact (rej_ok _ _ _ _).mp tail |>.elim

theorem lowerBound_recursive_typed (bound : Bound) (supported : RecursiveBound bound)
    {env : Core.TEnv} {start finish : Nat}
    (source : Core.tyBound env bound start = .ok ((), finish))
    {results : List Ty} {before after : LS} {value : Bnd}
    (run : lowerBound bound (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : BoundTyped after value := by
  cases bound with
  | omitted =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    trivial
  | expr expr | fromEnd expr =>
    obtain ⟨intTy, childFinish, childSource⟩ := tyBound_child source
    simp only [lowerBound] at run
    obtain ⟨result, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨intTy, lowerExpr_recursive_typed expr supported childSource childRun live⟩

theorem lowerExprs_recursive_typed (exprs : List Expr) (supported : RecursiveExpressions exprs)
    {env : Core.TEnv} {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    {results : List Ty} {before after : LS} {values : List ValueId}
    (run : lowerExprs exprs (lowerEnv env.mod env.vars results) before = (values, after))
    (live : after.cur.isSome = true) : TypedValues after types values := by
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
      obtain ⟨exprSupported, restSupported⟩ := supported
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
        have restTyped := lowerExprs_recursive_typed rest restSupported source restRun live
        have middleLive := (dead_lowerExprs rest).live_before restRun live
        have childTyped := lowerExpr_recursive_typed expr exprSupported childSource childRun middleLive
        have retained := types_lowerExprs rest _ _ _ _ restRun value (.data expected) childTyped
        exact .cons retained restTyped
      · simp [equal, chk] at source

theorem lowerArgs_recursive_typed (args : List Arg) (supported : RecursiveArguments args)
    {env : Core.TEnv} {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    {results : List Ty} {before after : LS} {values : List ValueId}
    (run : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, after))
    (live : after.cur.isSome = true) :
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
        obtain ⟨childSupported, restSupported⟩ := supported
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        simp only [lowerArgs] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        have restTyped := lowerArgs_recursive_typed args restSupported (by simpa using sameLength)
          restSource restRun live
        have middleLive := (dead_lowerArgs args).live_before restRun live
        have lowering := childRun
        simp only [lowerArg] at lowering
        obtain ⟨address, placeAfter, placeRun, freezeRun⟩ := bind_eq.mp lowering
        have placeLive := (dead_borrowTo mu address).live_before freezeRun middleLive
        have childTyped : middle.vals[value]? = some (some (.data (.ref mu info.ty))) := by
          cases mu with
          | readOnly =>
            obtain ⟨actual, placeTyped⟩ := lowerPlace_recursive_typed place childSupported placeSource placeRun placeLive
            cases current : placeAfter.cur with
            | none => simp [current] at placeLive
            | some block =>
              have permission : actual.atLeast .readOnly = true := by cases actual <;> rfl
              have typed := lowerArg_byRef_typed_of_place placeRun placeTyped permission current
              rw [childRun] at typed
              exact typed
          | mutable =>
            cases place with
            | field owner index =>
              obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, _, _, _⟩ :=
                tyPlace_field_mutable_binding placeSource (writable rfl)
              have ownerLowering := placeRun
              simp only [lowerPlace] at ownerLowering
              obtain ⟨ownerValue, ownerState, ownerRun, emitted⟩ := bind_eq.mp ownerLowering
              have ownerLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted placeLive
              obtain ⟨actual, ownerTyped⟩ := lowerPlace_recursive_typed owner childSupported ownerSource ownerRun ownerLive
              cases current : ownerState.cur with
              | none => simp [current] at ownerLive
              | some block =>
                have typed := lowerPlace_field_mutable_typed_of_owner placeSource (writable rfl)
                  ownerSource ownerRun ownerTyped current
                rw [placeRun] at typed
                cases placeCurrent : placeAfter.cur with
                | none => simp [placeCurrent] at placeLive
                | some placeBlock =>
                  have frozen := lowerArg_byRef_typed_of_place (requested := .mutable) placeRun typed.2 (by rfl) placeCurrent
                  rw [childRun] at frozen
                  exact frozen
            | var x =>
              have initial := (dead_lowerPlace (.var x)).live_before placeRun placeLive
              cases current : before.cur with
              | none => simp [current] at initial
              | some block =>
                have placeTyped := lowerPlace_var_exact placeSource results before current
                rw [placeRun] at placeTyped
                have permission : (if info.referenceWritable env.mod.profile then Mutability.mutable else .readOnly).atLeast .mutable = true := by
                  simp [writable rfl, Mutability.atLeast]
                have typed := lowerArg_byRef_typed_of_place placeRun
                  (by simpa only [referenceType] using placeTyped.2) permission (placeTyped.1.trans current)
                rw [childRun] at typed
                exact typed
            | global g =>
              have initial := (dead_lowerPlace (.global g)).live_before placeRun placeLive
              cases current : before.cur with
              | none => simp [current] at initial
              | some block =>
                have placeTyped := lowerPlace_global_exact placeSource env.vars results before current
                rw [placeRun] at placeTyped
                have permission : (if info.referenceWritable env.mod.profile then Mutability.mutable else .readOnly).atLeast .mutable = true := by
                  simp [writable rfl, Mutability.atLeast]
                have typed := lowerArg_byRef_typed_of_place placeRun
                  (by simpa only [referenceType] using placeTyped.2) permission (placeTyped.1.trans current)
                rw [childRun] at typed
                exact typed
            | deref expr =>
              have typed := lowerPlace_deref_writable_typed_of_child placeSource (writable rfl) placeRun placeLive
                (fun childFinish childSource => lowerExpr_recursive_typed expr childSupported childSource placeRun placeLive)
              cases current : placeAfter.cur with
              | none => simp [current] at placeLive
              | some block =>
                have frozen := lowerArg_byRef_typed_of_place (requested := .mutable) placeRun typed (by rfl) current
                rw [childRun] at frozen
                exact frozen
            | elem view index origin =>
              cases view with
              | of owner => contradiction
              | val expr =>
                obtain ⟨exprSupported, indexSupported⟩ := childSupported
                have typed := lowerPlace_elem_val_writable_typed_of_children placeSource (writable rfl) placeRun placeLive
                  (fun _ _ _ _ childSource childRun childLive => lowerExpr_recursive_typed expr exprSupported childSource childRun childLive)
                  (fun _ _ _ _ _ _ childSource childRun childLive => lowerExpr_recursive_typed index indexSupported childSource childRun childLive)
                cases current : placeAfter.cur with
                | none => simp [current] at placeLive
                | some block =>
                  have frozen := lowerArg_byRef_typed_of_place (requested := .mutable) placeRun typed (by rfl) current
                  rw [childRun] at frozen
                  exact frozen
        have retained := types_lowerArgs args _ _ _ _ restRun value (.data (.ref mu info.ty)) childTyped
        exact .cons ⟨.ref mu info.ty, retained, by simpa [tyOfVar, row] using permission⟩ restTyped
      | byVal expr =>
        obtain ⟨exprSupported, argsSupported⟩ := supported
        obtain ⟨localVar, argTy, childStart, childFinish, restStart,
          row, childSource, permission, restSource⟩ := tyArgs_byVal_head source
        simp only [lowerArgs, lowerArg] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        have restTyped := lowerArgs_recursive_typed args argsSupported (by simpa using sameLength)
          restSource restRun live
        have middleLive := (dead_lowerArgs args).live_before restRun live
        have childTyped := lowerExpr_recursive_typed expr exprSupported childSource childRun middleLive
        have retained := types_lowerArgs args _ _ _ _ restRun value (.data argTy) childTyped
        exact .cons ⟨argTy, retained, by simpa [tyOfVar, row] using permission⟩ restTyped

theorem lowerBlock_recursive_typed (body : Core.Block) (supported : RecursiveBlock body)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
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
            rw [← sameEnv] at valueRun
            exact lowerExpr_recursive_typed e supported source valueRun valueLive
      have retained := types_emitEffect (.leave scope) _ _ _ _ leaveRun result (.data ty) resultTyped
      exact types_popScope _ _ _ _ popRun result (.data ty) retained


end

end Goose.Lower.Validation
