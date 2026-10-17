import Goose.Lower.Validation.SummaryPreservationReturnFramesLoops

namespace Goose.Lower.Validation.SummaryPreservation.ReturnFrames

open Goose.Core Goose.GIR Goose.Lower.Validation

variable {avoid : List ValueId × Option OriginId}

mutual

theorem returnAbsent_lowerExpr : ∀ e : Expr, ReturnFreeExpr e → ReturnAbsentRun (avoid := avoid) (lowerExpr e)
  | .structLit t es, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExprs es (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .lit t n, free => by simp only [lowerExpr]; exact returnAbsent_emitDef _
  | .bool b, free => by simp only [lowerExpr]; exact returnAbsent_emitDef _
  | .read p, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .ref m p, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnAbsent_borrowTo m r
  | .slice m v lo hi org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerBound lo (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_lowerBound hi (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .len v, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .un op e org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun a => ReturnAbsentRun.bind (returnAbsent_intTyOf a) fun _ => returnAbsent_emitDef _
  | .bin op a b org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => ReturnAbsentRun.bind (returnAbsent_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun y =>
      ReturnAbsentRun.bind (returnAbsent_intTyOf x) fun _ => returnAbsent_emitDef _
  | .cmp op a b, free => by
    simp only [lowerExpr]
    refine ReturnAbsentRun.bind (returnAbsent_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => ReturnAbsentRun.bind (returnAbsent_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun y =>
      ReturnAbsentRun.bind (returnAbsent_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact returnAbsent_emitDef _
    | view _ _ => exact returnAbsent_emitDef _
  | .and a b, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => returnAbsent_shortCircuit true x (returnAbsent_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerExpr b)
  | .or a b, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun x => returnAbsent_shortCircuit false x (returnAbsent_lowerExpr b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerExpr b)
  | .not e, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .conv k target e org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun a => ReturnAbsentRun.bind (returnAbsent_intTyOf a) fun _ => returnAbsent_emitDef _
  | .call c args org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerArgs args (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun values => returnAbsent_call c values (some org)
  | .push owner e org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      returnAbsent_emitDef (.push r v org)
  | .pop owner org, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .ifE c t f, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv =>
      returnAbsent_ifE_core cv (sourceBlockScope t)
        (returnAbsent_lowerBlock none [] true t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
        (returnAbsent_lowerBlock none [] true f (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .blockE b, free => by
    simp only [lowerExpr]
    exact returnAbsent_lowerBlock none [] true b (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .arrLit t es, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExprs es (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .fill t e, free => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _

theorem returnAbsent_lowerExprs : ∀ es : List Expr, ReturnFreeExprs es → ReturnAbsentRun (avoid := avoid) (lowerExprs es)
  | [], free => by simp only [lowerExprs]; exact returnAbsent_pure _
  | e :: rest, free => by
    simp only [lowerExprs]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerExprs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _

theorem returnAbsent_lowerArg : ∀ a : Arg, ReturnFreeArg a → ReturnAbsentRun (avoid := avoid) (lowerArg a)
  | .byVal e, free => by simp only [lowerArg]; exact returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .byRef m p, free => by
    simp only [lowerArg]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnAbsent_borrowTo m r

theorem returnAbsent_lowerArgs : ∀ as : List Arg, ReturnFreeArgs as → ReturnAbsentRun (avoid := avoid) (lowerArgs as)
  | [], free => by simp only [lowerArgs]; exact returnAbsent_pure _
  | a :: rest, free => by
    simp only [lowerArgs]
    exact ReturnAbsentRun.bind (returnAbsent_lowerArg a (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _

theorem returnAbsent_lowerPlace : ∀ p : Place, ReturnFreePlace p → ReturnAbsentRun (avoid := avoid) (lowerPlace p)
  | .field owner i, free => by
    simp only [lowerPlace]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .var x, free => by simp only [lowerPlace]; exact returnAbsent_emitDef _
  | .global g, free => by simp only [lowerPlace]; exact returnAbsent_emitDef _
  | .deref e, free => by simp only [lowerPlace]; exact returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .elem v i org, free => by
    simp only [lowerPlace]
    exact ReturnAbsentRun.bind (returnAbsent_lowerView v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerExpr i (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _

theorem returnAbsent_lowerView : ∀ v : View, ReturnFreeView v → ReturnAbsentRun (avoid := avoid) (lowerView v)
  | .of p, free => by
    simp only [lowerView]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _
  | .val e, free => by
    simp only [lowerView]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitDef _

theorem returnAbsent_lowerBound : ∀ b : Bound, ReturnFreeBound b → ReturnAbsentRun (avoid := avoid) (lowerBound b)
  | .omitted, free => by simp only [lowerBound]; exact returnAbsent_pure _
  | .expr e, free => by
    simp only [lowerBound]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _
  | .fromEnd e, free => by
    simp only [lowerBound]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _

theorem returnAbsent_lowerEachSource : ∀ v : View, ReturnFreeView v → ReturnAbsentRun (avoid := avoid) (lowerEachSource v)
  | .of p, free => by
    simp only [lowerEachSource]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_pure _
  | .val e, free => by
    simp only [lowerEachSource]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_pure _

theorem returnAbsent_lowerBlockValue (want : Bool) : ∀ v : Option Expr, ReturnFreeValue v → ReturnAbsentRun (avoid := avoid) (lowerBlockValue want v)
  | some e, free => by simp only [lowerBlockValue]; exact returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | none, free => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact returnAbsent_pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact returnAbsent_emitDef _

theorem returnAbsent_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, ReturnFreeBlock b → ReturnAbsentRun (avoid := avoid) (lowerBlock lc pre want b)
  | .mk sc stmts value, free => by
    simp only [lowerBlock]
    exact ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ => returnAbsent_inScope sc
      (ReturnAbsentRun.bind (returnAbsent_initSlots _) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerStmts lc stmts (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
        ReturnAbsentRun.bind (returnAbsent_lowerBlockValue want value (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ =>
        returnAbsent_pure _)

theorem returnAbsent_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, ReturnFreeStmts ss → ReturnAbsentRun (avoid := avoid) (lowerStmts lc ss)
  | [], free => by simp only [lowerStmts]; exact returnAbsent_pure _
  | s :: rest, free => by
    simp only [lowerStmts]
    refine ReturnAbsentRun.bind (returnAbsent_isLive) fun live => ?_
    cases live
    · exact returnAbsent_pure _
    · exact ReturnAbsentRun.bind (returnAbsent_lowerStmt lc s (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_lowerStmts lc rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)

theorem returnAbsent_lowerPrintArgs : ∀ as : List PrintArg, ReturnFreePrintArgs as → ReturnAbsentRun (avoid := avoid) (lowerPrintArgs as)
  | [], free => by simp only [lowerPrintArgs]; exact returnAbsent_pure _
  | .text s :: rest, free => by
    simp only [lowerPrintArgs]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPrintArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _
  | .expr e :: rest, free => by
    simp only [lowerPrintArgs]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerPrintArgs rest (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _

theorem returnAbsent_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, ReturnFreeStmt s → ReturnAbsentRun (avoid := avoid) (lowerStmt lc s)
  | .letS x e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      ReturnAbsentRun.bind (returnAbsent_coerceSlot x v org) fun _ => returnAbsent_emitEffect _
  | .assign p e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitEffect _
  | .assignOp op p e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace p (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_intTyOf _) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_emitEffect _
  | .rebind x e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
      ReturnAbsentRun.bind (returnAbsent_coerceSlot x v org) fun _ =>
        ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_emitEffect _
  | .expr e _, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_pure _
  | .append owner src org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => ReturnAbsentRun.bind (returnAbsent_lowerView src (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ =>
      returnAbsent_emitEffect _
  | .popN owner count org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnAbsentRun.bind (returnAbsent_lowerExpr count (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      returnAbsent_emitEffect (.popN r n (some org))
  | .resize owner size none org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnAbsentRun.bind (returnAbsent_lowerExpr size (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      ReturnAbsentRun.bind (returnAbsent_pure _) fun fill => returnAbsent_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => ReturnAbsentRun.bind (returnAbsent_lowerExpr size (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun n =>
      ReturnAbsentRun.bind (returnAbsent_lowerExpr fill (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun v =>
        returnAbsent_emitEffect (.resize r n (some v) (some org))
  | .clear owner org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r => returnAbsent_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPlace owner (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun r =>
      ReturnAbsentRun.bind (returnAbsent_emitEffect (.clear r (some org))) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_lowerExpr replacement (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun run =>
        returnAbsent_emitEffect (.replace r run (some org))
  | .ifS c t f _, free => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (returnAbsent_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv => returnAbsent_ifS_none_core cv (returnAbsent_lowerBlock lc [] false t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (returnAbsent_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv =>
        returnAbsent_ifS_some_core cv (returnAbsent_lowerBlock lc [] false t (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) (returnAbsent_lowerBlock lc [] false fb (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .while c body _, free => by
    simp only [lowerStmt]
    apply returnAbsent_header0 (tail := fun header => lowerWhile header (lowerExpr c)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body))
    intro header
    exact returnAbsent_lowerWhile header (returnAbsent_lowerExpr c (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
      (fun depth exit => returnAbsent_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .forRange x lo hi body org, free => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (returnAbsent_lowerExpr lo (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun first =>
      ReturnAbsentRun.bind (returnAbsent_lowerExpr hi (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun bound =>
      returnAbsent_whenLive _ fun _ => ReturnAbsentRun.bind (returnAbsent_intTyOf first) fun ty => ?_
    apply returnAbsent_header1 (.data (.int ty)) first
      (tail := fun header counter => lowerRange ty counter bound header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body))
    intro header counter
    exact returnAbsent_lowerRange ty counter bound header
      (fun depth exit => returnAbsent_lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2))
  | .forEach x none v byRef body org, free => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (returnAbsent_lowerEachSource v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun ownerView =>
      ReturnAbsentRun.bind (returnAbsent_regrowOf _) fun regrow =>
      ReturnAbsentRun.bind (returnAbsent_eachSampled _ _) fun sampled =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun first =>
      returnAbsent_whenLive _ fun _ => ?_
    apply returnAbsent_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: []) false body))
    intro header counter
    apply returnAbsent_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun element =>
      ReturnAbsentRun.bind (returnAbsent_eachElemValue _ _ _) fun value => ?_
    exact returnAbsent_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .forEach x (some index) v byRef body org, free => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (returnAbsent_lowerEachSource v (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun ownerView =>
      ReturnAbsentRun.bind (returnAbsent_regrowOf _) fun regrow =>
      ReturnAbsentRun.bind (returnAbsent_eachSampled _ _) fun sampled =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun first =>
      returnAbsent_whenLive _ fun _ => ?_
    apply returnAbsent_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: [(index, counter, org)]) false body))
    intro header counter
    apply returnAbsent_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun element =>
      ReturnAbsentRun.bind (returnAbsent_eachElemValue _ _ _) fun value => ?_
    exact returnAbsent_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)
  | .ret e org, free => by exact False.elim free
  | .brk _, free => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnAbsent_pure _
    | some context =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
        returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .cont _, free => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnAbsent_pure _
    | some context =>
      cases kind : context.cont with
      | jump header =>
        simp only [lowerStmt, kind]
        exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
          returnAbsent_emitTerm _ (by intro values origin h; cases h)
      | next header ty counter =>
        simp only [lowerStmt, kind]
        exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
          ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ =>
            returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .print args org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerPrintArgs args (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitEffect _
  | .assertS e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun cv => returnAbsent_assert_core cv org
  | .abort _ org, free => by
    simp only [lowerStmt]
    exact returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .exit e org, free => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (returnAbsent_lowerExpr e (by first | exact free | exact free.1 | exact free.2 | exact free.1.1 | exact free.1.2 | exact free.2.1 | exact free.2.2 | exact free.2.2.1 | exact free.2.2.2)) fun _ => returnAbsent_emitTerm _ (by intro values origin h; cases h)

end

end Goose.Lower.Validation.SummaryPreservation.ReturnFrames
