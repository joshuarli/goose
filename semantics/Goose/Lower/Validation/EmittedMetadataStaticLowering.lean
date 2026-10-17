import Goose.Lower.Validation.EmittedMetadataStaticResolvedHelpers
import Goose.Lower.Validation.EmittedMetadataStaticSyntax

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

section
variable {module : Core.Module} {le : LEnv} (tables : EmittedStaticTables module le)
include tables

mutual

theorem resolved_lowerExpr : ∀ e : Expr, ResolvedExprAnnotations module e → EmittedResolvedRun module le (lowerExpr e)
  | .structLit t es => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExprs es (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .lit t n => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]; exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .bool b => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]; exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .read p => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .ref m p => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => resolved_borrowTo tables m r
  | .slice m v lo hi org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerBound lo (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      EmittedResolvedRun.bind (resolved_lowerBound hi (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .len v => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .un op e org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedResolvedRun.bind (resolved_intTyOf tables a) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .bin op a b org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => EmittedResolvedRun.bind (resolved_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun y =>
      EmittedResolvedRun.bind (resolved_intTyOf tables x) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .cmp op a b => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    refine EmittedResolvedRun.bind (resolved_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => EmittedResolvedRun.bind (resolved_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun y =>
      EmittedResolvedRun.bind (resolved_valTy module le x) fun t => ?_
    cases t with
    | data t => cases t <;> exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
    | view _ _ => exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .and a b => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => resolved_shortCircuit tables true x (resolved_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .or a b => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun x => resolved_shortCircuit tables false x (resolved_lowerExpr b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .not e => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .conv k target e org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedResolvedRun.bind (resolved_intTyOf tables a) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .call c args org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerArgs args (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun r => EmittedResolvedRun.bind (resolved_read module le) fun readEnv => by
        cases readEnv.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact EmittedResolvedRun.pure module le _ | exact EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => EmittedResolvedRun.pure module le _
  | .push owner e org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun v =>
      resolved_emitDef tables (.push r v org) (fun _ => trivial)
  | .pop owner org => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .ifE c t f => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun cv =>
      resolved_ifE_core tables cv (resolved_lowerBlock none [] true t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) (resolved_lowerBlock none [] true f (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2))
  | .blockE b => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact resolved_lowerBlock none [] true b (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .arrLit t es => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExprs es (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .fill t e => by
    intro annotations
    try simp only [ResolvedExprAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExpr]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem resolved_lowerExprs : ∀ es : List Expr, ResolvedExprsAnnotations module es → EmittedResolvedRun module le (lowerExprs es)
  | [] => by
    intro annotations
    try simp only [ResolvedExprsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExprs]; exact EmittedResolvedRun.pure module le _
  | e :: rest => by
    intro annotations
    try simp only [ResolvedExprsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerExprs]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerExprs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_lowerArg : ∀ a : Arg, ResolvedArgAnnotations module a → EmittedResolvedRun module le (lowerArg a)
  | .byVal e => by
    intro annotations
    try simp only [ResolvedArgAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerArg]; exact resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .byRef m p => by
    intro annotations
    try simp only [ResolvedArgAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerArg]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => resolved_borrowTo tables m r

theorem resolved_lowerArgs : ∀ as : List Arg, ResolvedArgsAnnotations module as → EmittedResolvedRun module le (lowerArgs as)
  | [] => by
    intro annotations
    try simp only [ResolvedArgsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerArgs]; exact EmittedResolvedRun.pure module le _
  | a :: rest => by
    intro annotations
    try simp only [ResolvedArgsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerArgs]
    exact EmittedResolvedRun.bind (resolved_lowerArg a (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_lowerPlace : ∀ p : Place, ResolvedPlaceAnnotations module p → EmittedResolvedRun module le (lowerPlace p)
  | .field owner i => by
    intro annotations
    try simp only [ResolvedPlaceAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPlace]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .var x => by
    intro annotations
    try simp only [ResolvedPlaceAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .global g => by
    intro annotations
    try simp only [ResolvedPlaceAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .deref e => by
    intro annotations
    try simp only [ResolvedPlaceAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPlace]; exact resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | .elem v i org => by
    intro annotations
    try simp only [ResolvedPlaceAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPlace]
    exact EmittedResolvedRun.bind (resolved_lowerView v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerExpr i (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem resolved_lowerView : ∀ v : View, ResolvedViewAnnotations module v → EmittedResolvedRun module le (lowerView v)
  | .of p => by
    intro annotations
    try simp only [ResolvedViewAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerView]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)
  | .val e => by
    intro annotations
    try simp only [ResolvedViewAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerView]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem resolved_lowerBound : ∀ b : Bound, ResolvedBoundAnnotations module b → EmittedResolvedRun module le (lowerBound b)
  | .omitted => by
    intro annotations
    try simp only [ResolvedBoundAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerBound]; exact EmittedResolvedRun.pure module le _
  | .expr e => by
    intro annotations
    try simp only [ResolvedBoundAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerBound]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _
  | .fromEnd e => by
    intro annotations
    try simp only [ResolvedBoundAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerBound]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_lowerEachSource : ∀ v : View, ResolvedViewAnnotations module v → EmittedResolvedRun module le (lowerEachSource v)
  | .of p => by
    intro annotations
    try simp only [ResolvedViewAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerEachSource]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => EmittedResolvedRun.pure module le _
  | .val e => by
    intro annotations
    try simp only [ResolvedViewAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerEachSource]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_lowerBlockValue (want : Bool) : ∀ v : Option Expr, ResolvedOptionalAnnotations module v → EmittedResolvedRun module le (lowerBlockValue want v)
  | some e => by
    intro annotations
    try simp only [ResolvedOptionalAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerBlockValue]; exact resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)
  | none => by
    intro annotations
    try simp only [ResolvedOptionalAnnotations, ResolvedOptionalAnnotations] at annotations
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact EmittedResolvedRun.pure module le _
    · simp only [lowerBlockValue, ↓reduceIte]; exact resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)

theorem resolved_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, ResolvedBlockAnnotations module b → EmittedResolvedRun module le (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    intro annotations
    try simp only [ResolvedBlockAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerBlock]
    exact EmittedResolvedRun.bind (resolved_emitEffect _) fun _ => resolved_inScope tables sc
      (EmittedResolvedRun.bind (resolved_initSlots tables _) fun _ => EmittedResolvedRun.bind (resolved_lowerStmts lc stmts (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
        EmittedResolvedRun.bind (resolved_lowerBlockValue want value (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_emitEffect _) fun _ =>
        EmittedResolvedRun.pure module le _)

theorem resolved_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, ResolvedStmtsAnnotations module ss → EmittedResolvedRun module le (lowerStmts lc ss)
  | [] => by
    intro annotations
    try simp only [ResolvedStmtsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmts]; exact EmittedResolvedRun.pure module le _
  | s :: rest => by
    intro annotations
    try simp only [ResolvedStmtsAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmts]
    refine EmittedResolvedRun.bind (resolved_isLive tables) fun live => ?_
    cases live
    · exact EmittedResolvedRun.pure module le _
    · exact EmittedResolvedRun.bind (resolved_lowerStmt lc s (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_lowerStmts lc rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)

theorem resolved_lowerPrintArgs : ∀ as : List PrintArg, ResolvedPrintAnnotations module as → EmittedResolvedRun module le (lowerPrintArgs as)
  | [] => by
    intro annotations
    try simp only [ResolvedPrintAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]; exact EmittedResolvedRun.pure module le _
  | .text s :: rest => by
    intro annotations
    try simp only [ResolvedPrintAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]
    exact EmittedResolvedRun.bind (resolved_lowerPrintArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _
  | .expr e :: rest => by
    intro annotations
    try simp only [ResolvedPrintAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerPrintArgs]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerPrintArgs rest (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, ResolvedStmtAnnotations module s → EmittedResolvedRun module le (lowerStmt lc s)
  | .letS x e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
      EmittedResolvedRun.bind (resolved_coerceSlot tables x value org) fun _ => resolved_emitEffect _
  | .assign p e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitEffect _
  | .assignOp op p e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace p (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ =>
      EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_intTyOf tables _) fun _ =>
      EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => resolved_emitEffect _
  | .rebind x e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
      EmittedResolvedRun.bind (resolved_coerceSlot tables x value org) fun _ =>
        EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => resolved_emitEffect _
  | .expr e _ => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.pure module le _
  | .append owner src org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => EmittedResolvedRun.bind (resolved_lowerView src (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ =>
      resolved_emitEffect _
  | .popN owner count org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedResolvedRun.bind (resolved_lowerExpr count (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      resolved_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedResolvedRun.bind (resolved_lowerExpr size (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      EmittedResolvedRun.bind (EmittedResolvedRun.pure module le _) fun fill => resolved_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => EmittedResolvedRun.bind (resolved_lowerExpr size (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun n =>
      EmittedResolvedRun.bind (resolved_lowerExpr fill (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun v =>
        resolved_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r => resolved_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPlace owner (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun r =>
      EmittedResolvedRun.bind (resolved_emitEffect (.clear r (some org))) fun _ =>
      EmittedResolvedRun.bind (resolved_lowerExpr replacement (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun run =>
        resolved_emitEffect (.replace r run (some org))
  | .ifS c t none _ => by
    intro annotations
    simp only [ResolvedStmtAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2)) fun cv =>
      resolved_ifS_none_core tables cv (resolved_lowerBlock lc [] false t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
  | .ifS c t (some fb) _ => by
    intro annotations
    simp only [ResolvedStmtAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2)) fun cv =>
      resolved_ifS_some_core tables cv (resolved_lowerBlock lc [] false t (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
        (resolved_lowerBlock lc [] false fb (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2))
  | .while c body _ => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact resolved_header0 tables (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => resolved_lowerWhile tables hb (resolved_lowerExpr c (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) (fun d xb => resolved_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .forRange x lo hi body org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    refine EmittedResolvedRun.bind (resolved_lowerExpr lo (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun a => EmittedResolvedRun.bind (resolved_lowerExpr hi (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun b =>
      resolved_whenLive tables _ fun _ => EmittedResolvedRun.bind (resolved_intTyOf tables a) fun t => ?_
    exact resolved_header1 tables (.data (.int t)) a (by rfl) (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => resolved_lowerRange tables t i b hb (fun d xb => resolved_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .forEach x idx v byRef body org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    refine EmittedResolvedRun.bind (resolved_lowerEachSource v (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun ov => EmittedResolvedRun.bind (resolved_regrowOf tables _) fun regrow =>
      EmittedResolvedRun.bind (resolved_eachSampled tables _ _) fun sampled => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun startAt =>
      resolved_whenLive tables _ fun _ => ?_
    exact resolved_header1 tables (.data (.int .i64)) startAt (by rfl) (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => resolved_lowerEach tables regrow ov.1 sampled hb i (fun d xb =>
        EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun elem => EmittedResolvedRun.bind (resolved_eachElemValue tables _ _ _) fun ev =>
          resolved_lowerBlock _ _ _ body (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)))
  | .ret e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun value =>
        EmittedResolvedRun.bind (resolved_coerceResult tables value org) fun _ =>
          EmittedResolvedRun.bind (EmittedResolvedRun.pure module le _) fun _ =>
            EmittedResolvedRun.bind (resolved_leaveTo tables 0) fun _ => resolved_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact EmittedResolvedRun.bind (EmittedResolvedRun.pure module le _) fun _ => EmittedResolvedRun.bind (resolved_leaveTo tables 0) fun _ => resolved_emitTerm _
  | .brk _ => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    cases lc with
    | none => simp only [lowerStmt]; exact EmittedResolvedRun.pure module le _
    | some l =>
      simp only [lowerStmt]
      exact EmittedResolvedRun.bind (resolved_leaveTo tables _) fun _ => resolved_emitTerm _
  | .cont _ => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    cases lc with
    | none => simp only [lowerStmt]; exact EmittedResolvedRun.pure module le _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact EmittedResolvedRun.bind (resolved_leaveTo tables _) fun _ => resolved_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact EmittedResolvedRun.bind (resolved_leaveTo tables _) fun _ => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => by first | trivial | exact annotations.1)) fun _ => resolved_emitTerm _
  | .print args org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerPrintArgs args (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitEffect _
  | .assertS e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun cv => resolved_assert_core tables cv org
  | .abort _ org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact resolved_emitTerm _
  | .exit e org => by
    intro annotations
    try simp only [ResolvedStmtAnnotations, ResolvedOptionalAnnotations] at annotations
    simp only [lowerStmt]
    exact EmittedResolvedRun.bind (resolved_lowerExpr e (by first | exact annotations | exact annotations.1 | exact annotations.2 | exact annotations.2.1 | exact annotations.2.2 | exact annotations.2.2.1 | exact annotations.2.2.2)) fun _ => resolved_emitTerm _

end

end

end Goose.Lower.Validation
