import Goose.Lower.Validation.CfgReturnFreeLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Lower.Validation

mutual

theorem returnFree_lowerExpr : ∀ e : Expr, ReturnFreeExpr e → ReturnFreeRun (lowerExpr e)
  | .structLit t es, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExprs es (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .lit t n, free => by simp only [lowerExpr]; exact returnFree_emitDef _
  | .bool b, free => by simp only [lowerExpr]; exact returnFree_emitDef _
  | .read p, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .ref m p, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnFree_borrowTo m r
  | .slice m v lo hi org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerBound lo (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
      ReturnFreeRun.bind (returnFree_lowerBound hi (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .len v, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .un op e org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun a => ReturnFreeRun.bind (returnFree_intTyOf a) fun _ => returnFree_emitDef _
  | .bin op a b org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => ReturnFreeRun.bind (returnFree_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun y =>
      ReturnFreeRun.bind (returnFree_intTyOf x) fun _ => returnFree_emitDef _
  | .cmp op a b, free => by
    simp only [lowerExpr]
    refine ReturnFreeRun.bind (returnFree_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => ReturnFreeRun.bind (returnFree_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun y =>
      ReturnFreeRun.bind (returnFree_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact returnFree_emitDef _
    | view _ _ => exact returnFree_emitDef _
  | .and a b, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => returnFree_shortCircuit true x (returnFree_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerExpr b)
  | .or a b, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => returnFree_shortCircuit false x (returnFree_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerExpr b)
  | .not e, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .conv k target e org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun a => ReturnFreeRun.bind (returnFree_intTyOf a) fun _ => returnFree_emitDef _
  | .call c args org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerArgs args (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun values => returnFree_call c values (some org)
  | .push owner e org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      returnFree_emitDef (.push r v org)
  | .pop owner org, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .ifE c t f, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv =>
      returnFree_ifE_core cv (sourceBlockScope t)
        (returnFree_lowerBlock none [] true t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
        (returnFree_lowerBlock none [] true f (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .blockE b, free => by
    simp only [lowerExpr]
    exact returnFree_lowerBlock none [] true b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .arrLit t es, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExprs es (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .fill t e, free => by
    simp only [lowerExpr]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _

theorem returnFree_lowerExprs : ∀ es : List Expr, ReturnFreeExprs es → ReturnFreeRun (lowerExprs es)
  | [], free => by simp only [lowerExprs]; exact returnFree_pure _
  | e :: rest, free => by
    simp only [lowerExprs]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerExprs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _

theorem returnFree_lowerArg : ∀ a : Arg, ReturnFreeArg a → ReturnFreeRun (lowerArg a)
  | .byVal e, free => by simp only [lowerArg]; exact returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .byRef m p, free => by
    simp only [lowerArg]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnFree_borrowTo m r

theorem returnFree_lowerArgs : ∀ as : List Arg, ReturnFreeArgs as → ReturnFreeRun (lowerArgs as)
  | [], free => by simp only [lowerArgs]; exact returnFree_pure _
  | a :: rest, free => by
    simp only [lowerArgs]
    exact ReturnFreeRun.bind (returnFree_lowerArg a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _

theorem returnFree_lowerPlace : ∀ p : Place, ReturnFreePlace p → ReturnFreeRun (lowerPlace p)
  | .field owner i, free => by
    simp only [lowerPlace]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .var x, free => by simp only [lowerPlace]; exact returnFree_emitDef _
  | .global g, free => by simp only [lowerPlace]; exact returnFree_emitDef _
  | .deref e, free => by simp only [lowerPlace]; exact returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .elem v i org, free => by
    simp only [lowerPlace]
    exact ReturnFreeRun.bind (returnFree_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerExpr i (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _

theorem returnFree_lowerView : ∀ v : View, ReturnFreeView v → ReturnFreeRun (lowerView v)
  | .of p, free => by
    simp only [lowerView]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _
  | .val e, free => by
    simp only [lowerView]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitDef _

theorem returnFree_lowerBound : ∀ b : Bound, ReturnFreeBound b → ReturnFreeRun (lowerBound b)
  | .omitted, free => by simp only [lowerBound]; exact returnFree_pure _
  | .expr e, free => by
    simp only [lowerBound]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _
  | .fromEnd e, free => by
    simp only [lowerBound]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _

theorem returnFree_lowerEachSource : ∀ v : View, ReturnFreeView v → ReturnFreeRun (lowerEachSource v)
  | .of p, free => by
    simp only [lowerEachSource]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_emitDef _) fun _ => returnFree_pure _
  | .val e, free => by
    simp only [lowerEachSource]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_emitDef _) fun _ => returnFree_pure _

theorem returnFree_lowerBlockValue (want : Bool) : ∀ v : Option Expr, ReturnFreeValue v → ReturnFreeRun (lowerBlockValue want v)
  | some e, free => by simp only [lowerBlockValue]; exact returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | none, free => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact returnFree_pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact returnFree_emitDef _

theorem returnFree_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, ReturnFreeBlock b → ReturnFreeRun (lowerBlock lc pre want b)
  | .mk sc stmts value, free => by
    simp only [lowerBlock]
    exact ReturnFreeRun.bind (returnFree_emitEffect _) fun _ => returnFree_inScope sc
      (ReturnFreeRun.bind (returnFree_initSlots _) fun _ => ReturnFreeRun.bind (returnFree_lowerStmts lc stmts (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
        ReturnFreeRun.bind (returnFree_lowerBlockValue want value (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_emitEffect _) fun _ =>
        returnFree_pure _)

theorem returnFree_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, ReturnFreeStmts ss → ReturnFreeRun (lowerStmts lc ss)
  | [], free => by simp only [lowerStmts]; exact returnFree_pure _
  | s :: rest, free => by
    simp only [lowerStmts]
    refine ReturnFreeRun.bind (returnFree_isLive) fun live => ?_
    cases live
    · exact returnFree_pure _
    · exact ReturnFreeRun.bind (returnFree_lowerStmt lc s (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_lowerStmts lc rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)

theorem returnFree_lowerPrintArgs : ∀ as : List PrintArg, ReturnFreePrintArgs as → ReturnFreeRun (lowerPrintArgs as)
  | [], free => by simp only [lowerPrintArgs]; exact returnFree_pure _
  | .text s :: rest, free => by
    simp only [lowerPrintArgs]
    exact ReturnFreeRun.bind (returnFree_lowerPrintArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _
  | .expr e :: rest, free => by
    simp only [lowerPrintArgs]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerPrintArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _

theorem returnFree_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, ReturnFreeStmt s → ReturnFreeRun (lowerStmt lc s)
  | .letS x e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      ReturnFreeRun.bind (returnFree_coerceSlot x v org) fun _ => returnFree_emitEffect _
  | .assign p e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitEffect _
  | .assignOp op p e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_emitDef _) fun _ =>
      ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_intTyOf _) fun _ =>
      ReturnFreeRun.bind (returnFree_emitDef _) fun _ => returnFree_emitEffect _
  | .rebind x e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      ReturnFreeRun.bind (returnFree_coerceSlot x v org) fun _ =>
        ReturnFreeRun.bind (returnFree_emitDef _) fun _ => returnFree_emitEffect _
  | .expr e _, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_pure _
  | .append owner src org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnFreeRun.bind (returnFree_lowerView src (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
      returnFree_emitEffect _
  | .popN owner count org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnFreeRun.bind (returnFree_lowerExpr count (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      returnFree_emitEffect (.popN r n (some org))
  | .resize owner size none org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnFreeRun.bind (returnFree_lowerExpr size (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      ReturnFreeRun.bind (returnFree_pure _) fun fill => returnFree_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnFreeRun.bind (returnFree_lowerExpr size (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      ReturnFreeRun.bind (returnFree_lowerExpr fill (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
        returnFree_emitEffect (.resize r n (some v) (some org))
  | .clear owner org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnFree_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r =>
      ReturnFreeRun.bind (returnFree_emitEffect (.clear r (some org))) fun _ =>
      ReturnFreeRun.bind (returnFree_lowerExpr replacement (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun run =>
        returnFree_emitEffect (.replace r run (some org))
  | .ifS c t f _, free => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact ReturnFreeRun.bind (returnFree_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv => returnFree_ifS_none_core cv (returnFree_lowerBlock lc [] false t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact ReturnFreeRun.bind (returnFree_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv =>
        returnFree_ifS_some_core cv (returnFree_lowerBlock lc [] false t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (returnFree_lowerBlock lc [] false fb (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .while c body _, free => by
    simp only [lowerStmt]
    apply returnFree_header0 (tail := fun header => lowerWhile header (lowerExpr c)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body))
    intro header
    exact returnFree_lowerWhile header (returnFree_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
      (fun depth exit => returnFree_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .forRange x lo hi body org, free => by
    simp only [lowerStmt]
    refine ReturnFreeRun.bind (returnFree_lowerExpr lo (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun first =>
      ReturnFreeRun.bind (returnFree_lowerExpr hi (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun bound =>
      returnFree_whenLive _ fun _ => ReturnFreeRun.bind (returnFree_intTyOf first) fun ty => ?_
    apply returnFree_header1 (.data (.int ty)) first
      (tail := fun header counter => lowerRange ty counter bound header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body))
    intro header counter
    exact returnFree_lowerRange ty counter bound header
      (fun depth exit => returnFree_lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .forEach x none v byRef body org, free => by
    simp only [lowerStmt]
    refine ReturnFreeRun.bind (returnFree_lowerEachSource v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun ownerView =>
      ReturnFreeRun.bind (returnFree_regrowOf _) fun regrow =>
      ReturnFreeRun.bind (returnFree_eachSampled _ _) fun sampled =>
      ReturnFreeRun.bind (returnFree_emitDef _) fun first =>
      returnFree_whenLive _ fun _ => ?_
    apply returnFree_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: []) false body))
    intro header counter
    apply returnFree_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnFreeRun.bind (returnFree_emitDef _) fun element =>
      ReturnFreeRun.bind (returnFree_eachElemValue _ _ _) fun value => ?_
    exact returnFree_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .forEach x (some index) v byRef body org, free => by
    simp only [lowerStmt]
    refine ReturnFreeRun.bind (returnFree_lowerEachSource v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun ownerView =>
      ReturnFreeRun.bind (returnFree_regrowOf _) fun regrow =>
      ReturnFreeRun.bind (returnFree_eachSampled _ _) fun sampled =>
      ReturnFreeRun.bind (returnFree_emitDef _) fun first =>
      returnFree_whenLive _ fun _ => ?_
    apply returnFree_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: [(index, counter, org)]) false body))
    intro header counter
    apply returnFree_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnFreeRun.bind (returnFree_emitDef _) fun element =>
      ReturnFreeRun.bind (returnFree_eachElemValue _ _ _) fun value => ?_
    exact returnFree_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .ret e org, free => by exact False.elim free
  | .brk _, free => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnFree_pure _
    | some context =>
      simp only [lowerStmt]
      exact ReturnFreeRun.bind (returnFree_leaveTo _) fun _ =>
        returnFree_emitTerm _ (by intro values origin h; cases h)
  | .cont _, free => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnFree_pure _
    | some context =>
      cases kind : context.cont with
      | jump header =>
        simp only [lowerStmt, kind]
        exact ReturnFreeRun.bind (returnFree_leaveTo _) fun _ =>
          returnFree_emitTerm _ (by intro values origin h; cases h)
      | next header ty counter =>
        simp only [lowerStmt, kind]
        exact ReturnFreeRun.bind (returnFree_leaveTo _) fun _ =>
          ReturnFreeRun.bind (returnFree_emitDef _) fun _ =>
            returnFree_emitTerm _ (by intro values origin h; cases h)
  | .print args org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerPrintArgs args (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitEffect _
  | .assertS e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv => returnFree_assert_core cv org
  | .abort _ org, free => by
    simp only [lowerStmt]
    exact returnFree_emitTerm _ (by intro values origin h; cases h)
  | .exit e org, free => by
    simp only [lowerStmt]
    exact ReturnFreeRun.bind (returnFree_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnFree_emitTerm _ (by intro values origin h; cases h)

end

end Goose.Lower.Validation
