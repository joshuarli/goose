import Goose.Lower.Validation.CfgUnreachableLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Lower.Validation

mutual

theorem unreachable_lowerExpr : ∀ e : Expr, UnreachableRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExprs es) fun _ => unreachable_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact unreachable_emitDef _
  | .bool b => by simp only [lowerExpr]; exact unreachable_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun _ => unreachable_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun r => unreachable_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerView v) fun _ => UnreachableRun.bind (unreachable_lowerBound lo) fun _ =>
      UnreachableRun.bind (unreachable_lowerBound hi) fun _ => unreachable_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerView v) fun _ => unreachable_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun a => UnreachableRun.bind (unreachable_intTyOf a) fun _ => unreachable_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr a) fun x => UnreachableRun.bind (unreachable_lowerExpr b) fun y =>
      UnreachableRun.bind (unreachable_intTyOf x) fun _ => unreachable_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine UnreachableRun.bind (unreachable_lowerExpr a) fun x => UnreachableRun.bind (unreachable_lowerExpr b) fun y =>
      UnreachableRun.bind (unreachable_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact unreachable_emitDef _
    | view _ _ => exact unreachable_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr a) fun x => unreachable_shortCircuit true x (unreachable_lowerExpr b) (advB_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr a) fun x => unreachable_shortCircuit false x (unreachable_lowerExpr b) (advB_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun a => UnreachableRun.bind (unreachable_intTyOf a) fun _ => unreachable_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerArgs args) fun values => unreachable_call c values (some org)
  | .push owner e org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r => UnreachableRun.bind (unreachable_lowerExpr e) fun v =>
      unreachable_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun _ => unreachable_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr c) fun cv =>
      unreachable_ifE_core cv (unreachable_lowerBlock none [] true t) (unreachable_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact unreachable_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExprs es) fun _ => unreachable_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_emitDef _

theorem unreachable_lowerExprs : ∀ es : List Expr, UnreachableRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact unreachable_pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => UnreachableRun.bind (unreachable_lowerExprs rest) fun _ => unreachable_pure _

theorem unreachable_lowerArg : ∀ a : Arg, UnreachableRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact unreachable_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun r => unreachable_borrowTo m r

theorem unreachable_lowerArgs : ∀ as : List Arg, UnreachableRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact unreachable_pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact UnreachableRun.bind (unreachable_lowerArg a) fun _ => UnreachableRun.bind (unreachable_lowerArgs rest) fun _ => unreachable_pure _

theorem unreachable_lowerPlace : ∀ p : Place, UnreachableRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun _ => unreachable_emitDef _
  | .var x => by simp only [lowerPlace]; exact unreachable_emitDef _
  | .global g => by simp only [lowerPlace]; exact unreachable_emitDef _
  | .deref e => by simp only [lowerPlace]; exact unreachable_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact UnreachableRun.bind (unreachable_lowerView v) fun _ => UnreachableRun.bind (unreachable_lowerExpr i) fun _ => unreachable_emitDef _

theorem unreachable_lowerView : ∀ v : View, UnreachableRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun _ => unreachable_emitDef _
  | .val e => by
    simp only [lowerView]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_emitDef _

theorem unreachable_lowerBound : ∀ b : Bound, UnreachableRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact unreachable_pure _
  | .expr e => by
    simp only [lowerBound]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_pure _

theorem unreachable_lowerEachSource : ∀ v : View, UnreachableRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun _ => UnreachableRun.bind (unreachable_emitDef _) fun _ => unreachable_pure _
  | .val e => by
    simp only [lowerEachSource]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => UnreachableRun.bind (unreachable_emitDef _) fun _ => unreachable_pure _

theorem unreachable_lowerBlockValue (want : Bool) : ∀ v : Option Expr, UnreachableRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact unreachable_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact unreachable_pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact unreachable_emitDef _

theorem unreachable_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, UnreachableRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact UnreachableRun.bind (unreachable_emitEffect _) fun _ => unreachable_inScope sc
      (UnreachableRun.bind (unreachable_initSlots _) fun _ => UnreachableRun.bind (unreachable_lowerStmts lc stmts) fun _ =>
        UnreachableRun.bind (unreachable_lowerBlockValue want value) fun _ => UnreachableRun.bind (unreachable_emitEffect _) fun _ =>
        unreachable_pure _)

theorem unreachable_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, UnreachableRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact unreachable_pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine UnreachableRun.bind (unreachable_isLive) fun live => ?_
    cases live
    · exact unreachable_pure _
    · exact UnreachableRun.bind (unreachable_lowerStmt lc s) fun _ => unreachable_lowerStmts lc rest

theorem unreachable_lowerPrintArgs : ∀ as : List PrintArg, UnreachableRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact unreachable_pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact UnreachableRun.bind (unreachable_lowerPrintArgs rest) fun _ => unreachable_pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => UnreachableRun.bind (unreachable_lowerPrintArgs rest) fun _ => unreachable_pure _

theorem unreachable_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, UnreachableRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun v =>
      UnreachableRun.bind (unreachable_coerceSlot x v org) fun _ => unreachable_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun _ => UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace p) fun _ => UnreachableRun.bind (unreachable_emitDef _) fun _ =>
      UnreachableRun.bind (unreachable_lowerExpr e) fun _ => UnreachableRun.bind (unreachable_intTyOf _) fun _ =>
      UnreachableRun.bind (unreachable_emitDef _) fun _ => unreachable_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun v =>
      UnreachableRun.bind (unreachable_coerceSlot x v org) fun _ =>
        UnreachableRun.bind (unreachable_emitDef _) fun _ => unreachable_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun _ => UnreachableRun.bind (unreachable_lowerView src) fun _ =>
      unreachable_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r => UnreachableRun.bind (unreachable_lowerExpr count) fun n =>
      unreachable_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r => UnreachableRun.bind (unreachable_lowerExpr size) fun n =>
      UnreachableRun.bind (unreachable_pure _) fun fill => unreachable_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r => UnreachableRun.bind (unreachable_lowerExpr size) fun n =>
      UnreachableRun.bind (unreachable_lowerExpr fill) fun v =>
        unreachable_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r => unreachable_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPlace owner) fun r =>
      UnreachableRun.bind (unreachable_emitEffect (.clear r (some org))) fun _ =>
      UnreachableRun.bind (unreachable_lowerExpr replacement) fun run =>
        unreachable_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact UnreachableRun.bind (unreachable_lowerExpr c) fun cv => unreachable_ifS_none_core cv (unreachable_lowerBlock lc [] false t) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact UnreachableRun.bind (unreachable_lowerExpr c) fun cv =>
        unreachable_ifS_some_core cv (unreachable_lowerBlock lc [] false t) (unreachable_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    apply unreachable_header0 (tail := fun header => lowerWhile header (lowerExpr c)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body))
    intro header
    exact unreachable_lowerWhile header (unreachable_lowerExpr c)
      (fun depth exit => unreachable_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine UnreachableRun.bind (unreachable_lowerExpr lo) fun first =>
      UnreachableRun.bind (unreachable_lowerExpr hi) fun bound =>
      unreachable_whenLive _ fun _ => UnreachableRun.bind (unreachable_intTyOf first) fun ty => ?_
    apply unreachable_header1 (.data (.int ty)) first
      (tail := fun header counter => lowerRange ty counter bound header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body))
    intro header counter
    exact unreachable_lowerRange ty counter bound header
      (fun depth exit => unreachable_lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body)
  | .forEach x none v byRef body org => by
    simp only [lowerStmt]
    refine UnreachableRun.bind (unreachable_lowerEachSource v) fun ownerView =>
      UnreachableRun.bind (unreachable_regrowOf _) fun regrow =>
      UnreachableRun.bind (unreachable_eachSampled _ _) fun sampled =>
      UnreachableRun.bind (unreachable_emitDef _) fun first =>
      unreachable_whenLive _ fun _ => ?_
    apply unreachable_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: []) false body))
    intro header counter
    apply unreachable_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine UnreachableRun.bind (unreachable_emitDef _) fun element =>
      UnreachableRun.bind (unreachable_eachElemValue _ _ _) fun value => ?_
    exact unreachable_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body
  | .forEach x (some index) v byRef body org => by
    simp only [lowerStmt]
    refine UnreachableRun.bind (unreachable_lowerEachSource v) fun ownerView =>
      UnreachableRun.bind (unreachable_regrowOf _) fun regrow =>
      UnreachableRun.bind (unreachable_eachSampled _ _) fun sampled =>
      UnreachableRun.bind (unreachable_emitDef _) fun first =>
      unreachable_whenLive _ fun _ => ?_
    apply unreachable_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: [(index, counter, org)]) false body))
    intro header counter
    apply unreachable_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine UnreachableRun.bind (unreachable_emitDef _) fun element =>
      UnreachableRun.bind (unreachable_eachElemValue _ _ _) fun value => ?_
    exact unreachable_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) _ false body
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact UnreachableRun.bind (unreachable_lowerExpr e) fun v => UnreachableRun.bind (unreachable_coerceResult v org) fun _ =>
        UnreachableRun.bind (unreachable_pure _) fun _ => UnreachableRun.bind (unreachable_leaveTo 0) fun _ => unreachable_emitTerm _ (by intro h; cases h)
    | none =>
      simp only [lowerStmt]
      exact UnreachableRun.bind (unreachable_pure _) fun _ => UnreachableRun.bind (unreachable_leaveTo 0) fun _ => unreachable_emitTerm _ (by intro h; cases h)
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact unreachable_pure _
    | some context =>
      simp only [lowerStmt]
      exact UnreachableRun.bind (unreachable_leaveTo _) fun _ =>
        unreachable_emitTerm _ (by intro h; cases h)
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact unreachable_pure _
    | some context =>
      cases kind : context.cont with
      | jump header =>
        simp only [lowerStmt, kind]
        exact UnreachableRun.bind (unreachable_leaveTo _) fun _ =>
          unreachable_emitTerm _ (by intro h; cases h)
      | next header ty counter =>
        simp only [lowerStmt, kind]
        exact UnreachableRun.bind (unreachable_leaveTo _) fun _ =>
          UnreachableRun.bind (unreachable_emitDef _) fun _ =>
            unreachable_emitTerm _ (by intro h; cases h)
  | .print args org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerPrintArgs args) fun _ => unreachable_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun cv => unreachable_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact unreachable_emitTerm _ (by intro h; cases h)
  | .exit e org => by
    simp only [lowerStmt]
    exact UnreachableRun.bind (unreachable_lowerExpr e) fun _ => unreachable_emitTerm _ (by intro h; cases h)

end

end Goose.Lower.Validation
