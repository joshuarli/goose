import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesControl

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

mutual

theorem recipes_lowerExpr : ∀ e : Expr, RecipeRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExprs es) fun _ => recipes_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact recipes_emitDef _
  | .bool b => by simp only [lowerExpr]; exact recipes_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerPlace p) fun _ => recipes_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerPlace p) fun r => recipes_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerView v) fun _ => RecipeRun.bind (recipes_lowerBound lo) fun _ =>
      RecipeRun.bind (recipes_lowerBound hi) fun _ => recipes_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerView v) fun _ => recipes_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr e) fun a => RecipeRun.bind (recipes_intTyOf a) fun _ => recipes_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr a) fun x => RecipeRun.bind (recipes_lowerExpr b) fun y =>
      RecipeRun.bind (recipes_intTyOf x) fun _ => recipes_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine RecipeRun.bind (recipes_lowerExpr a) fun x => RecipeRun.bind (recipes_lowerExpr b) fun y =>
      RecipeRun.bind (recipes_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact recipes_emitDef _
    | view _ _ => exact recipes_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr a) fun x => recipes_shortCircuit true x (recipes_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr a) fun x => recipes_shortCircuit false x (recipes_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => recipes_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr e) fun a => RecipeRun.bind (recipes_intTyOf a) fun _ => recipes_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerArgs args) fun _ =>
      RecipeRun.bind (recipes_emitDef _) fun r => RecipeRun.bind recipes_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact RecipeRun.pure _ | exact RecipeRun.bind (recipes_emitTerm _) fun _ => RecipeRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r => RecipeRun.bind (recipes_lowerExpr e) fun v =>
      recipes_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun _ => recipes_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr c) fun cv =>
      recipes_ifE_core cv (sourceBlockScope t) (recipes_lowerBlock none [] true t) (recipes_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact recipes_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExprs es) fun _ => recipes_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => recipes_emitDef _

theorem recipes_lowerExprs : ∀ es : List Expr, RecipeRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact RecipeRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.bind (recipes_lowerExprs rest) fun _ => RecipeRun.pure _

theorem recipes_lowerArg : ∀ a : Arg, RecipeRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact recipes_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact RecipeRun.bind (recipes_lowerPlace p) fun r => recipes_borrowTo m r

theorem recipes_lowerArgs : ∀ as : List Arg, RecipeRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact RecipeRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact RecipeRun.bind (recipes_lowerArg a) fun _ => RecipeRun.bind (recipes_lowerArgs rest) fun _ => RecipeRun.pure _

theorem recipes_lowerPlace : ∀ p : Place, RecipeRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun _ => recipes_emitDef _
  | .var x => by simp only [lowerPlace]; exact recipes_emitDef _
  | .global g => by simp only [lowerPlace]; exact recipes_emitDef _
  | .deref e => by simp only [lowerPlace]; exact recipes_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact RecipeRun.bind (recipes_lowerView v) fun _ => RecipeRun.bind (recipes_lowerExpr i) fun _ => recipes_emitDef _

theorem recipes_lowerView : ∀ v : View, RecipeRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact RecipeRun.bind (recipes_lowerPlace p) fun _ => recipes_emitDef _
  | .val e => by
    simp only [lowerView]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => recipes_emitDef _

theorem recipes_lowerBound : ∀ b : Bound, RecipeRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact RecipeRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.pure _

theorem recipes_lowerEachSource : ∀ v : View, RecipeRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact RecipeRun.bind (recipes_lowerPlace p) fun _ => RecipeRun.bind (recipes_emitDef _) fun _ => RecipeRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.bind (recipes_emitDef _) fun _ => RecipeRun.pure _

theorem recipes_lowerBlockValue (want : Bool) : ∀ v : Option Expr, RecipeRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact recipes_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact RecipeRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact recipes_emitDef _

theorem recipes_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, RecipeRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact RecipeRun.bind (recipes_emitEffect _) fun _ => recipes_inScope sc
      (RecipeRun.bind (recipes_initSlots _) fun _ => RecipeRun.bind (recipes_lowerStmts lc stmts) fun _ =>
        RecipeRun.bind (recipes_lowerBlockValue want value) fun _ => RecipeRun.bind (recipes_emitEffect _) fun _ =>
        RecipeRun.pure _)

theorem recipes_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, RecipeRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact RecipeRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine RecipeRun.bind recipes_isLive fun live => ?_
    cases live
    · exact RecipeRun.pure _
    · exact RecipeRun.bind (recipes_lowerStmt lc s) fun _ => recipes_lowerStmts lc rest

theorem recipes_lowerPrintArgs : ∀ as : List PrintArg, RecipeRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact RecipeRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact RecipeRun.bind (recipes_lowerPrintArgs rest) fun _ => RecipeRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.bind (recipes_lowerPrintArgs rest) fun _ => RecipeRun.pure _

theorem recipes_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, RecipeRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerExpr e) fun value =>
      RecipeRun.bind (recipes_coerceSlot x value org) fun _ => recipes_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace p) fun _ => RecipeRun.bind (recipes_lowerExpr e) fun _ => recipes_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace p) fun _ => RecipeRun.bind (recipes_emitDef _) fun _ =>
      RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.bind (recipes_intTyOf _) fun _ =>
      RecipeRun.bind (recipes_emitDef _) fun _ => recipes_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerExpr e) fun value =>
      RecipeRun.bind (recipes_coerceSlot x value org) fun _ =>
        RecipeRun.bind (recipes_emitDef _) fun _ => recipes_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => RecipeRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun _ => RecipeRun.bind (recipes_lowerView src) fun _ =>
      recipes_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r => RecipeRun.bind (recipes_lowerExpr count) fun n =>
      recipes_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r => RecipeRun.bind (recipes_lowerExpr size) fun n =>
      RecipeRun.bind (RecipeRun.pure _) fun fill => recipes_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r => RecipeRun.bind (recipes_lowerExpr size) fun n =>
      RecipeRun.bind (recipes_lowerExpr fill) fun v =>
        recipes_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r => recipes_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPlace owner) fun r =>
      RecipeRun.bind (recipes_emitEffect (.clear r (some org))) fun _ =>
      RecipeRun.bind (recipes_lowerExpr replacement) fun run =>
        recipes_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact RecipeRun.bind (recipes_lowerExpr c) fun cv => recipes_ifS_none_core cv (recipes_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact RecipeRun.bind (recipes_lowerExpr c) fun cv =>
        recipes_ifS_some_core cv (recipes_lowerBlock lc [] false t) (recipes_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact recipes_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => recipes_lowerWhile hb (recipes_lowerExpr c) (fun d xb => recipes_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine RecipeRun.bind (recipes_lowerExpr lo) fun a => RecipeRun.bind (recipes_lowerExpr hi) fun b =>
      recipes_whenLive _ fun _ => RecipeRun.bind (recipes_intTyOf a) fun t => ?_
    exact recipes_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => recipes_lowerRange t i b hb (fun d xb => recipes_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine RecipeRun.bind (recipes_lowerEachSource v) fun ov => RecipeRun.bind (recipes_regrowOf _) fun regrow =>
      RecipeRun.bind (recipes_eachSampled _ _) fun sampled => RecipeRun.bind (recipes_emitDef _) fun startAt =>
      recipes_whenLive _ fun _ => ?_
    exact recipes_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => recipes_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        RecipeRun.bind (recipes_emitDef _) fun elem => RecipeRun.bind (recipes_eachElemValue _ _ _) fun ev =>
          recipes_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact RecipeRun.bind (recipes_lowerExpr e) fun value =>
        RecipeRun.bind (recipes_coerceResult value org) fun _ =>
          RecipeRun.bind (RecipeRun.pure _) fun _ =>
            RecipeRun.bind (recipes_leaveTo 0) fun _ => recipes_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact RecipeRun.bind (RecipeRun.pure _) fun _ => RecipeRun.bind (recipes_leaveTo 0) fun _ => recipes_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact RecipeRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact RecipeRun.bind (recipes_leaveTo _) fun _ => recipes_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact RecipeRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact RecipeRun.bind (recipes_leaveTo _) fun _ => recipes_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact RecipeRun.bind (recipes_leaveTo _) fun _ => RecipeRun.bind (recipes_emitDef _) fun _ => recipes_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerPrintArgs args) fun _ => recipes_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerExpr e) fun cv => recipes_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact recipes_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact RecipeRun.bind (recipes_lowerExpr e) fun _ => recipes_emitTerm _

end


theorem recipes_finishFunction (impl : Impl) (value : ValueId) :
    RecipeRun (finishFunction impl value) := by
  unfold finishFunction
  refine RecipeRun.bind recipes_read fun le =>
    RecipeRun.bind recipes_isLive fun live => ?_
  cases live
  · exact RecipeRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ↓reduceIte]
      exact RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
        RecipeRun.bind (recipes_emitTerm _) fun _ =>
        RecipeRun.bind (recipes_setCur _) fun _ => recipes_emitTerm _
    · simp only [sink, ↓reduceIte]
      exact recipes_emitTerm _


#print axioms recipes_lowerExpr
#print axioms recipes_lowerPlace
#print axioms recipes_lowerView
#print axioms recipes_lowerBlock
#print axioms recipes_lowerStmt

end Goose.Lower.Validation.SourceCanonicalRootFloors
