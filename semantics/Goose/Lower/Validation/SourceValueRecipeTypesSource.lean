import Goose.Lower.Validation.SourceValueRecipeTypesControl

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

mutual

theorem recipeTypes_lowerExpr : ∀ e : Expr, RecipeTypeRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExprs es) fun _ => recipeTypes_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact recipeTypes_emitDef _
  | .bool b => by simp only [lowerExpr]; exact recipeTypes_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun address =>
      RecipeTypeRun.bind (recipeTypes_emitDef (.load address)) fun value =>
      RecipeTypeRun.bind (recipeTypes_recordReadValueRootRecipe value p) fun _ => RecipeTypeRun.pure value
  | .ref m p => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun r => recipeTypes_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerView v) fun _ => RecipeTypeRun.bind (recipeTypes_lowerBound lo) fun _ =>
      RecipeTypeRun.bind (recipeTypes_lowerBound hi) fun _ => recipeTypes_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerView v) fun _ => recipeTypes_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun a => RecipeTypeRun.bind (recipeTypes_intTyOf a) fun _ => recipeTypes_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr a) fun x => RecipeTypeRun.bind (recipeTypes_lowerExpr b) fun y =>
      RecipeTypeRun.bind (recipeTypes_intTyOf x) fun _ => recipeTypes_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine RecipeTypeRun.bind (recipeTypes_lowerExpr a) fun x => RecipeTypeRun.bind (recipeTypes_lowerExpr b) fun y =>
      RecipeTypeRun.bind (recipeTypes_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact recipeTypes_emitDef _
    | view _ _ => exact recipeTypes_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr a) fun x => recipeTypes_shortCircuit true x (recipeTypes_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr a) fun x => recipeTypes_shortCircuit false x (recipeTypes_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => recipeTypes_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun a => RecipeTypeRun.bind (recipeTypes_intTyOf a) fun _ => recipeTypes_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerArgs args) fun _ =>
      RecipeTypeRun.bind (recipeTypes_emitDef _) fun r => RecipeTypeRun.bind recipeTypes_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact RecipeTypeRun.pure _ | exact RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => RecipeTypeRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r => RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun v =>
      recipeTypes_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun _ => recipeTypes_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr c) fun cv =>
      recipeTypes_ifE_core cv (sourceBlockScope t) (recipeTypes_lowerBlock none [] true t) (recipeTypes_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact recipeTypes_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExprs es) fun _ => recipeTypes_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => recipeTypes_emitDef _

theorem recipeTypes_lowerExprs : ∀ es : List Expr, RecipeTypeRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact RecipeTypeRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.bind (recipeTypes_lowerExprs rest) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_lowerArg : ∀ a : Arg, RecipeTypeRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact recipeTypes_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun r => recipeTypes_borrowTo m r

theorem recipeTypes_lowerArgs : ∀ as : List Arg, RecipeTypeRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact RecipeTypeRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact RecipeTypeRun.bind (recipeTypes_lowerArg a) fun _ => RecipeTypeRun.bind (recipeTypes_lowerArgs rest) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_lowerPlace : ∀ p : Place, RecipeTypeRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun _ => recipeTypes_emitDef _
  | .var x => by simp only [lowerPlace]; exact recipeTypes_emitDef _
  | .global g => by simp only [lowerPlace]; exact recipeTypes_emitDef _
  | .deref e => by simp only [lowerPlace]; exact recipeTypes_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact RecipeTypeRun.bind (recipeTypes_lowerView v) fun _ => RecipeTypeRun.bind (recipeTypes_lowerExpr i) fun _ => recipeTypes_emitDef _

theorem recipeTypes_lowerView : ∀ v : View, RecipeTypeRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun _ => recipeTypes_emitDef _
  | .val e => by
    simp only [lowerView]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => recipeTypes_emitDef _

theorem recipeTypes_lowerBound : ∀ b : Bound, RecipeTypeRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact RecipeTypeRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_lowerEachSource : ∀ v : View, RecipeTypeRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun _ => RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => RecipeTypeRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_lowerBlockValue (want : Bool) : ∀ v : Option Expr, RecipeTypeRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact recipeTypes_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact RecipeTypeRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact recipeTypes_emitDef _

theorem recipeTypes_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, RecipeTypeRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact RecipeTypeRun.bind (recipeTypes_emitEffect _) fun _ => recipeTypes_inScope sc
      (RecipeTypeRun.bind (recipeTypes_initSlots _) fun _ => RecipeTypeRun.bind (recipeTypes_lowerStmts lc stmts) fun _ =>
        RecipeTypeRun.bind (recipeTypes_lowerBlockValue want value) fun _ => RecipeTypeRun.bind (recipeTypes_emitEffect _) fun _ =>
        RecipeTypeRun.pure _)

theorem recipeTypes_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, RecipeTypeRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact RecipeTypeRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine RecipeTypeRun.bind recipeTypes_isLive fun live => ?_
    cases live
    · exact RecipeTypeRun.pure _
    · exact RecipeTypeRun.bind (recipeTypes_lowerStmt lc s) fun _ => recipeTypes_lowerStmts lc rest

theorem recipeTypes_lowerPrintArgs : ∀ as : List PrintArg, RecipeTypeRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact RecipeTypeRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact RecipeTypeRun.bind (recipeTypes_lowerPrintArgs rest) fun _ => RecipeTypeRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.bind (recipeTypes_lowerPrintArgs rest) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, RecipeTypeRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun value =>
      RecipeTypeRun.bind (recipeTypes_coerceSlot x value org) fun _ => recipeTypes_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun _ => RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => recipeTypes_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace p) fun _ => RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ =>
      RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.bind (recipeTypes_intTyOf _) fun _ =>
      RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => recipeTypes_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun value =>
      RecipeTypeRun.bind (recipeTypes_coerceSlot x value org) fun _ =>
        RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => recipeTypes_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => RecipeTypeRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun _ => RecipeTypeRun.bind (recipeTypes_lowerView src) fun _ =>
      recipeTypes_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r => RecipeTypeRun.bind (recipeTypes_lowerExpr count) fun n =>
      recipeTypes_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r => RecipeTypeRun.bind (recipeTypes_lowerExpr size) fun n =>
      RecipeTypeRun.bind (RecipeTypeRun.pure _) fun fill => recipeTypes_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r => RecipeTypeRun.bind (recipeTypes_lowerExpr size) fun n =>
      RecipeTypeRun.bind (recipeTypes_lowerExpr fill) fun v =>
        recipeTypes_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r => recipeTypes_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPlace owner) fun r =>
      RecipeTypeRun.bind (recipeTypes_emitEffect (.clear r (some org))) fun _ =>
      RecipeTypeRun.bind (recipeTypes_lowerExpr replacement) fun run =>
        recipeTypes_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact RecipeTypeRun.bind (recipeTypes_lowerExpr c) fun cv => recipeTypes_ifS_none_core cv (recipeTypes_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact RecipeTypeRun.bind (recipeTypes_lowerExpr c) fun cv =>
        recipeTypes_ifS_some_core cv (recipeTypes_lowerBlock lc [] false t) (recipeTypes_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact recipeTypes_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => recipeTypes_lowerWhile hb (recipeTypes_lowerExpr c) (fun d xb => recipeTypes_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine RecipeTypeRun.bind (recipeTypes_lowerExpr lo) fun a => RecipeTypeRun.bind (recipeTypes_lowerExpr hi) fun b =>
      recipeTypes_whenLive _ fun _ => RecipeTypeRun.bind (recipeTypes_intTyOf a) fun t => ?_
    exact recipeTypes_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => recipeTypes_lowerRange t i b hb (fun d xb => recipeTypes_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine RecipeTypeRun.bind (recipeTypes_lowerEachSource v) fun ov => RecipeTypeRun.bind (recipeTypes_regrowOf _) fun regrow =>
      RecipeTypeRun.bind (recipeTypes_eachSampled _ _) fun sampled => RecipeTypeRun.bind (recipeTypes_emitDef _) fun startAt =>
      recipeTypes_whenLive _ fun _ => ?_
    exact recipeTypes_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => recipeTypes_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        RecipeTypeRun.bind (recipeTypes_emitDef _) fun elem => RecipeTypeRun.bind (recipeTypes_eachElemValue _ _ _) fun ev =>
          recipeTypes_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun value =>
        RecipeTypeRun.bind (recipeTypes_coerceResult value org) fun _ =>
          RecipeTypeRun.bind (RecipeTypeRun.pure _) fun _ =>
            RecipeTypeRun.bind (recipeTypes_leaveTo 0) fun _ => recipeTypes_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact RecipeTypeRun.bind (RecipeTypeRun.pure _) fun _ => RecipeTypeRun.bind (recipeTypes_leaveTo 0) fun _ => recipeTypes_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact RecipeTypeRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact RecipeTypeRun.bind (recipeTypes_leaveTo _) fun _ => recipeTypes_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact RecipeTypeRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact RecipeTypeRun.bind (recipeTypes_leaveTo _) fun _ => recipeTypes_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact RecipeTypeRun.bind (recipeTypes_leaveTo _) fun _ => RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => recipeTypes_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerPrintArgs args) fun _ => recipeTypes_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun cv => recipeTypes_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact recipeTypes_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact RecipeTypeRun.bind (recipeTypes_lowerExpr e) fun _ => recipeTypes_emitTerm _

end


theorem recipeTypes_finishFunction (impl : Impl) (value : ValueId) :
    RecipeTypeRun (finishFunction impl value) := by
  unfold finishFunction
  refine RecipeTypeRun.bind recipeTypes_read fun le =>
    RecipeTypeRun.bind recipeTypes_isLive fun live => ?_
  cases live
  · exact RecipeTypeRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ↓reduceIte]
      exact RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
        RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ =>
        RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => recipeTypes_emitTerm _
    · simp only [sink, ↓reduceIte]
      exact recipeTypes_emitTerm _


#print axioms recipeTypes_lowerExpr
#print axioms recipeTypes_lowerPlace
#print axioms recipeTypes_lowerView
#print axioms recipeTypes_lowerBlock
#print axioms recipeTypes_lowerStmt

end Goose.Lower.Validation.SourceValueRecipeTypes
