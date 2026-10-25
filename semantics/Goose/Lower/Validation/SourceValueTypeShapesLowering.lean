import Goose.Lower.Validation.SourceValueTypeShapesHelpers
import Goose.Lower.Validation.SourceValueTypeShapesSyntax

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

section
variable {module : Core.Module} {le : LEnv} (tables : ShapeTables module le)
include tables

mutual

theorem shaped_lowerExpr : ∀ e : Expr, ShapeExprAnnotations module e → EmittedShapeRun module le (lowerExpr e)
  | .structLit t es => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExprs es (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .lit t n => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]; exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .bool b => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]; exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .read p => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerPlace p annotations) fun address =>
      EmittedShapeRun.bind (shaped_emitDef tables (.load address) (fun _ => trivial)) fun value =>
        EmittedShapeRun.bind (shaped_recordReadValueRootRecipe (module := module) (le := le) value p) fun _ =>
          EmittedShapeRun.pure module le value
  | .ref m p => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => shaped_borrowTo tables m r
  | .slice m v lo hi org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerBound lo (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      EmittedShapeRun.bind (shaped_lowerBound hi (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .len v => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .un op e org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedShapeRun.bind (shaped_intTyOf tables a) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .bin op a b org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => EmittedShapeRun.bind (shaped_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun y =>
      EmittedShapeRun.bind (shaped_intTyOf tables x) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .cmp op a b => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    refine EmittedShapeRun.bind (shaped_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => EmittedShapeRun.bind (shaped_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun y =>
      EmittedShapeRun.bind (shaped_valTy module le x) fun t => ?_
    cases t with
    | data t => cases t <;> exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
    | view _ _ => exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .and a b => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => shaped_shortCircuit tables true x (shaped_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .or a b => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => shaped_shortCircuit tables false x (shaped_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .not e => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .conv k target e org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedShapeRun.bind (shaped_intTyOf tables a) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .call c args org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerArgs args (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun r => EmittedShapeRun.bind (shaped_read module le) fun readEnv => by
        cases readEnv.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact EmittedShapeRun.pure module le _ | exact EmittedShapeRun.bind (shaped_emitTerm _) fun _ => EmittedShapeRun.pure module le _
  | .push owner e org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun v =>
      shaped_emitDef tables (.push r v org) (fun _ => trivial)
  | .pop owner org => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .ifE c t f => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun cv =>
      shaped_ifE_recorded_core tables cv (sourceBlockScope t) (shaped_lowerBlock none [] true t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) (shaped_lowerBlock none [] true f (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .blockE b => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact shaped_lowerBlock none [] true b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .arrLit t es => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExprs es (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .fill t e => by
    intro annotations
    try simp only [ShapeExprAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem shaped_lowerExprs : ∀ es : List Expr, ShapeExprsAnnotations module es → EmittedShapeRun module le (lowerExprs es)
  | [] => by
    intro annotations
    try simp only [ShapeExprsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExprs]; exact EmittedShapeRun.pure module le _
  | e :: rest => by
    intro annotations
    try simp only [ShapeExprsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerExprs]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerExprs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _

theorem shaped_lowerArg : ∀ a : Arg, ShapeArgAnnotations module a → EmittedShapeRun module le (lowerArg a)
  | .byVal e => by
    intro annotations
    try simp only [ShapeArgAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerArg]; exact shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .byRef m p => by
    intro annotations
    try simp only [ShapeArgAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerArg]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => shaped_borrowTo tables m r

theorem shaped_lowerArgs : ∀ as : List Arg, ShapeArgsAnnotations module as → EmittedShapeRun module le (lowerArgs as)
  | [] => by
    intro annotations
    try simp only [ShapeArgsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerArgs]; exact EmittedShapeRun.pure module le _
  | a :: rest => by
    intro annotations
    try simp only [ShapeArgsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerArgs]
    exact EmittedShapeRun.bind (shaped_lowerArg a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _

theorem shaped_lowerPlace : ∀ p : Place, ShapePlaceAnnotations module p → EmittedShapeRun module le (lowerPlace p)
  | .field owner i => by
    intro annotations
    try simp only [ShapePlaceAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPlace]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .var x => by
    intro annotations
    try simp only [ShapePlaceAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .global g => by
    intro annotations
    try simp only [ShapePlaceAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .deref e => by
    intro annotations
    try simp only [ShapePlaceAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .elem v i org => by
    intro annotations
    try simp only [ShapePlaceAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPlace]
    exact EmittedShapeRun.bind (shaped_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerExpr i (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem shaped_lowerView : ∀ v : View, ShapeViewAnnotations module v → EmittedShapeRun module le (lowerView v)
  | .of p => by
    intro annotations
    try simp only [ShapeViewAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerView]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .val e => by
    intro annotations
    try simp only [ShapeViewAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerView]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem shaped_lowerBound : ∀ b : Bound, ShapeBoundAnnotations module b → EmittedShapeRun module le (lowerBound b)
  | .omitted => by
    intro annotations
    try simp only [ShapeBoundAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerBound]; exact EmittedShapeRun.pure module le _
  | .expr e => by
    intro annotations
    try simp only [ShapeBoundAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerBound]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _
  | .fromEnd e => by
    intro annotations
    try simp only [ShapeBoundAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerBound]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _

theorem shaped_lowerEachSource : ∀ v : View, ShapeViewAnnotations module v → EmittedShapeRun module le (lowerEachSource v)
  | .of p => by
    intro annotations
    try simp only [ShapeViewAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerEachSource]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => EmittedShapeRun.pure module le _
  | .val e => by
    intro annotations
    try simp only [ShapeViewAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerEachSource]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => EmittedShapeRun.pure module le _

theorem shaped_lowerBlockValue (want : Bool) : ∀ v : Option Expr, ShapeOptionalAnnotations module v → EmittedShapeRun module le (lowerBlockValue want v)
  | some e => by
    intro annotations
    try simp only [ShapeOptionalAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerBlockValue]; exact shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | none => by
    intro annotations
    try simp only [ShapeOptionalAnnotations, ShapeOptionalAnnotations] at annotations
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact EmittedShapeRun.pure module le _
    · simp only [lowerBlockValue, ↓reduceIte]; exact shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem shaped_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, ShapeBlockAnnotations module b → EmittedShapeRun module le (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    intro annotations
    try simp only [ShapeBlockAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerBlock]
    exact EmittedShapeRun.bind (shaped_emitEffect _) fun _ => shaped_inScope tables sc
      (EmittedShapeRun.bind (shaped_initSlots tables _) fun _ => EmittedShapeRun.bind (shaped_lowerStmts lc stmts (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
        EmittedShapeRun.bind (shaped_lowerBlockValue want value (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_emitEffect _) fun _ =>
        EmittedShapeRun.pure module le _)

theorem shaped_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, ShapeStmtsAnnotations module ss → EmittedShapeRun module le (lowerStmts lc ss)
  | [] => by
    intro annotations
    try simp only [ShapeStmtsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmts]; exact EmittedShapeRun.pure module le _
  | s :: rest => by
    intro annotations
    try simp only [ShapeStmtsAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmts]
    refine EmittedShapeRun.bind (shaped_isLive tables) fun live => ?_
    cases live
    · exact EmittedShapeRun.pure module le _
    · exact EmittedShapeRun.bind (shaped_lowerStmt lc s (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_lowerStmts lc rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)

theorem shaped_lowerPrintArgs : ∀ as : List PrintArg, ShapePrintAnnotations module as → EmittedShapeRun module le (lowerPrintArgs as)
  | [] => by
    intro annotations
    try simp only [ShapePrintAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]; exact EmittedShapeRun.pure module le _
  | .text s :: rest => by
    intro annotations
    try simp only [ShapePrintAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]
    exact EmittedShapeRun.bind (shaped_lowerPrintArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _
  | .expr e :: rest => by
    intro annotations
    try simp only [ShapePrintAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerPrintArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _

theorem shaped_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, ShapeStmtAnnotations module s → EmittedShapeRun module le (lowerStmt lc s)
  | .letS x e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
      EmittedShapeRun.bind (shaped_coerceSlot tables x value org) fun _ => shaped_emitEffect _
  | .assign p e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitEffect _
  | .assignOp op p e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ =>
      EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_intTyOf tables _) fun _ =>
      EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => shaped_emitEffect _
  | .rebind x e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
      EmittedShapeRun.bind (shaped_coerceSlot tables x value org) fun _ =>
        EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => shaped_emitEffect _
  | .expr e _ => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.pure module le _
  | .append owner src org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedShapeRun.bind (shaped_lowerView src (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      shaped_emitEffect _
  | .popN owner count org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedShapeRun.bind (shaped_lowerExpr count (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      shaped_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedShapeRun.bind (shaped_lowerExpr size (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      EmittedShapeRun.bind (EmittedShapeRun.pure module le _) fun fill => shaped_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedShapeRun.bind (shaped_lowerExpr size (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      EmittedShapeRun.bind (shaped_lowerExpr fill (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun v =>
        shaped_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => shaped_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r =>
      EmittedShapeRun.bind (shaped_emitEffect (.clear r (some org))) fun _ =>
      EmittedShapeRun.bind (shaped_lowerExpr replacement (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun run =>
        shaped_emitEffect (.replace r run (some org))
  | .ifS c t none _ => by
    intro annotations
    simp only [ShapeStmtAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2)) fun cv =>
      shaped_ifS_none_core tables cv (shaped_lowerBlock lc [] false t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
  | .ifS c t (some fb) _ => by
    intro annotations
    simp only [ShapeStmtAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2)) fun cv =>
      shaped_ifS_some_core tables cv (shaped_lowerBlock lc [] false t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
        (shaped_lowerBlock lc [] false fb (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
  | .while c body _ => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact shaped_header0 tables (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => shaped_lowerWhile tables hb (shaped_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) (fun d xb => shaped_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .forRange x lo hi body org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    refine EmittedShapeRun.bind (shaped_lowerExpr lo (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedShapeRun.bind (shaped_lowerExpr hi (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun b =>
      shaped_whenLive tables _ fun _ => EmittedShapeRun.bind (shaped_intTyOf tables a) fun t => ?_
    exact shaped_header1 tables (.data (.int t)) a (by simp [ValueTypeShape, DataTypeShape, Ty.storable]) (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => shaped_lowerRange tables t i b hb (fun d xb => shaped_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .forEach x idx v byRef body org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    refine EmittedShapeRun.bind (shaped_lowerEachSource v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun ov => EmittedShapeRun.bind (shaped_regrowOf tables _) fun regrow =>
      EmittedShapeRun.bind (shaped_eachSampled tables _ _) fun sampled => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun startAt =>
      shaped_whenLive tables _ fun _ => ?_
    exact shaped_header1 tables (.data (.int .i64)) startAt (by simp [ValueTypeShape, DataTypeShape, Ty.storable]) (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => shaped_lowerEach tables regrow ov.1 sampled hb i (fun d xb =>
        EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun elem => EmittedShapeRun.bind (shaped_eachElemValue tables _ _ _) fun ev =>
          shaped_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .ret e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
        EmittedShapeRun.bind (shaped_coerceResult tables value org) fun _ =>
          EmittedShapeRun.bind (EmittedShapeRun.pure module le _) fun _ =>
            EmittedShapeRun.bind (shaped_leaveTo tables 0) fun _ => shaped_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact EmittedShapeRun.bind (EmittedShapeRun.pure module le _) fun _ => EmittedShapeRun.bind (shaped_leaveTo tables 0) fun _ => shaped_emitTerm _
  | .brk _ => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    cases lc with
    | none => simp only [lowerStmt]; exact EmittedShapeRun.pure module le _
    | some l =>
      simp only [lowerStmt]
      exact EmittedShapeRun.bind (shaped_leaveTo tables _) fun _ => shaped_emitTerm _
  | .cont _ => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    cases lc with
    | none => simp only [lowerStmt]; exact EmittedShapeRun.pure module le _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact EmittedShapeRun.bind (shaped_leaveTo tables _) fun _ => shaped_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact EmittedShapeRun.bind (shaped_leaveTo tables _) fun _ => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => shaped_emitTerm _
  | .print args org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerPrintArgs args (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitEffect _
  | .assertS e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun cv => shaped_assert_core tables cv org
  | .abort _ org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact shaped_emitTerm _
  | .exit e org => by
    intro annotations
    try simp only [ShapeStmtAnnotations, ShapeOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedShapeRun.bind (shaped_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => shaped_emitTerm _

end

end

end Goose.Lower.Validation
