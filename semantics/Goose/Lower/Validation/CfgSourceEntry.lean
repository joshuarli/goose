import Goose.Lower.Validation.CfgEntryLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Lower.Validation

mutual

theorem entry_lowerExpr (lc : Option LoopCtx) : ∀ e : Expr, EntryRun lc (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExprs lc es) fun _ => entry_emitDef lc _
  | .lit t n => by simp only [lowerExpr]; exact entry_emitDef lc _
  | .bool b => by simp only [lowerExpr]; exact entry_emitDef lc _
  | .read p => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerPlace lc p) fun _ => entry_emitDef lc _
  | .ref m p => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerPlace lc p) fun r => entry_borrowTo lc m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerView lc v) fun _ => EntryRun.bind (entry_lowerBound lc lo) fun _ =>
      EntryRun.bind (entry_lowerBound lc hi) fun _ => entry_emitDef lc _
  | .len v => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerView lc v) fun _ => entry_emitDef lc _
  | .un op e org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc e) fun a => EntryRun.bind (entry_intTyOf lc a) fun _ => entry_emitDef lc _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc a) fun x => EntryRun.bind (entry_lowerExpr lc b) fun y =>
      EntryRun.bind (entry_intTyOf lc x) fun _ => entry_emitDef lc _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine EntryRun.bind (entry_lowerExpr lc a) fun x => EntryRun.bind (entry_lowerExpr lc b) fun y =>
      EntryRun.bind (entry_valTy lc x) fun t => ?_
    cases t with
    | data t => cases t <;> exact entry_emitDef lc _
    | view _ _ => exact entry_emitDef lc _
  | .and a b => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc a) fun x => entry_shortCircuit lc true x (entry_lowerExpr lc b) (advB_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc a) fun x => entry_shortCircuit lc false x (entry_lowerExpr lc b) (advB_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_emitDef lc _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc e) fun a => EntryRun.bind (entry_intTyOf lc a) fun _ => entry_emitDef lc _
  | .call c args org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerArgs lc args) fun _ => EntryRun.bind (entry_emitDef lc _) fun r => EntryRun.bind (entry_read lc) fun le => by
        cases hnr : le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact entry_pure lc _ | exact EntryRun.bind (entry_emitTerm lc _ (by simp [Term.successors])) fun _ => entry_pure lc _
  | .push owner e org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r => EntryRun.bind (entry_lowerExpr lc e) fun v =>
      entry_emitDef lc (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun _ => entry_emitDef lc _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc c) fun cv =>
      entry_ifE_core lc cv ((entry_lowerBlock none [] true t).withLoop (advB_lowerBlock none [] true t) lc) ((entry_lowerBlock none [] true f).withLoop (advB_lowerBlock none [] true f) lc)
  | .blockE b => by
    simp only [lowerExpr]
    exact (entry_lowerBlock none [] true b).withLoop (advB_lowerBlock none [] true b) lc
  | .arrLit t es => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExprs lc es) fun _ => entry_emitDef lc _
  | .fill t e => by
    simp only [lowerExpr]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_emitDef lc _

theorem entry_lowerExprs (lc : Option LoopCtx) : ∀ es : List Expr, EntryRun lc (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact entry_pure lc _
  | e :: rest => by
    simp only [lowerExprs]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => EntryRun.bind (entry_lowerExprs lc rest) fun _ => entry_pure lc _

theorem entry_lowerArg (lc : Option LoopCtx) : ∀ a : Arg, EntryRun lc (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact entry_lowerExpr lc e
  | .byRef m p => by
    simp only [lowerArg]
    exact EntryRun.bind (entry_lowerPlace lc p) fun r => entry_borrowTo lc m r

theorem entry_lowerArgs (lc : Option LoopCtx) : ∀ as : List Arg, EntryRun lc (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact entry_pure lc _
  | a :: rest => by
    simp only [lowerArgs]
    exact EntryRun.bind (entry_lowerArg lc a) fun _ => EntryRun.bind (entry_lowerArgs lc rest) fun _ => entry_pure lc _

theorem entry_lowerPlace (lc : Option LoopCtx) : ∀ p : Place, EntryRun lc (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun _ => entry_emitDef lc _
  | .var x => by simp only [lowerPlace]; exact entry_emitDef lc _
  | .global g => by simp only [lowerPlace]; exact entry_emitDef lc _
  | .deref e => by simp only [lowerPlace]; exact entry_lowerExpr lc e
  | .elem v i org => by
    simp only [lowerPlace]
    exact EntryRun.bind (entry_lowerView lc v) fun _ => EntryRun.bind (entry_lowerExpr lc i) fun _ => entry_emitDef lc _

theorem entry_lowerView (lc : Option LoopCtx) : ∀ v : View, EntryRun lc (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact EntryRun.bind (entry_lowerPlace lc p) fun _ => entry_emitDef lc _
  | .val e => by
    simp only [lowerView]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_emitDef lc _

theorem entry_lowerBound (lc : Option LoopCtx) : ∀ b : Bound, EntryRun lc (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact entry_pure lc _
  | .expr e => by
    simp only [lowerBound]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_pure lc _
  | .fromEnd e => by
    simp only [lowerBound]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_pure lc _

theorem entry_lowerEachSource (lc : Option LoopCtx) : ∀ v : View, EntryRun lc (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact EntryRun.bind (entry_lowerPlace lc p) fun _ => EntryRun.bind (entry_emitDef lc _) fun _ => entry_pure lc _
  | .val e => by
    simp only [lowerEachSource]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => EntryRun.bind (entry_emitDef lc _) fun _ => entry_pure lc _

theorem entry_lowerBlockValue (lc : Option LoopCtx) (want : Bool) : ∀ v : Option Expr, EntryRun lc (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact entry_lowerExpr lc e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact entry_pure lc _
    · simp only [lowerBlockValue, ↓reduceIte]; exact entry_emitDef lc _

theorem entry_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, EntryRun lc (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact EntryRun.bind (entry_emitEffect lc _) fun _ => entry_inScope sc
      (EntryRun.bind (entry_initSlots lc _) fun _ => EntryRun.bind (entry_lowerStmts lc stmts) fun _ =>
        EntryRun.bind (entry_lowerBlockValue lc want value) fun _ => EntryRun.bind (entry_emitEffect lc _) fun _ =>
        entry_pure lc _)

theorem entry_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, EntryRun lc (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact entry_pure lc _
  | s :: rest => by
    simp only [lowerStmts]
    refine EntryRun.bind (entry_isLive lc) fun live => ?_
    cases live
    · exact entry_pure lc _
    · exact EntryRun.bind (entry_lowerStmt lc s) fun _ => entry_lowerStmts lc rest

theorem entry_lowerPrintArgs (lc : Option LoopCtx) : ∀ as : List PrintArg, EntryRun lc (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact entry_pure lc _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact EntryRun.bind (entry_lowerPrintArgs lc rest) fun _ => entry_pure lc _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => EntryRun.bind (entry_lowerPrintArgs lc rest) fun _ => entry_pure lc _

theorem entry_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, EntryRun lc (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerExpr lc e) fun v =>
      EntryRun.bind (entry_coerceSlot lc x v org) fun _ => entry_emitEffect lc _
  | .assign p e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc p) fun _ => EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_emitEffect lc _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc p) fun _ => EntryRun.bind (entry_emitDef lc _) fun _ =>
      EntryRun.bind (entry_lowerExpr lc e) fun _ => EntryRun.bind (entry_intTyOf lc _) fun _ =>
      EntryRun.bind (entry_emitDef lc _) fun _ => entry_emitEffect lc _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerExpr lc e) fun v =>
      EntryRun.bind (entry_coerceSlot lc x v org) fun _ =>
        EntryRun.bind (entry_emitDef lc _) fun _ => entry_emitEffect lc _
  | .expr e _ => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_pure lc _
  | .append owner src org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun _ => EntryRun.bind (entry_lowerView lc src) fun _ =>
      entry_emitEffect lc _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r => EntryRun.bind (entry_lowerExpr lc count) fun n =>
      entry_emitEffect lc (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r => EntryRun.bind (entry_lowerExpr lc size) fun n =>
      EntryRun.bind (entry_pure lc _) fun fill => entry_emitEffect lc (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r => EntryRun.bind (entry_lowerExpr lc size) fun n =>
      EntryRun.bind (entry_lowerExpr lc fill) fun v =>
        entry_emitEffect lc (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r => entry_emitEffect lc (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPlace lc owner) fun r =>
      EntryRun.bind (entry_emitEffect lc (.clear r (some org))) fun _ =>
      EntryRun.bind (entry_lowerExpr lc replacement) fun run =>
        entry_emitEffect lc (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact EntryRun.bind (entry_lowerExpr lc c) fun cv => entry_ifS_none_core lc cv (entry_lowerBlock lc [] false t) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact EntryRun.bind (entry_lowerExpr lc c) fun cv =>
        entry_ifS_some_core lc cv (entry_lowerBlock lc [] false t) (entry_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    apply entry_header0 lc
      (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => advB_lowerWhile hb (advB_lowerExpr c) (fun d xb => advB_lowerBlock _ _ _ body))
    intro hb env before result after run bounded headerBound
    apply entry_lowerWhile hb (entry_lowerExpr none c) (advB_lowerExpr c)
      (fun d xb => advB_lowerBlock _ _ _ body) ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    exact (entry_lowerBlock (some ⟨depth, exit, .jump hb⟩) [] false body
      env before result after run bounded ⟨exitBound, headerBound⟩).1
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine EntryRun.bind (entry_lowerExpr lc lo) fun a =>
      EntryRun.bind (entry_lowerExpr lc hi) fun b =>
      entry_whenLive lc _ fun _ => EntryRun.bind (entry_intTyOf lc a) fun t => ?_
    apply entry_header1 lc (.data (.int t)) a
      (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => advB_lowerRange t i b hb (fun d xb => advB_lowerBlock _ _ _ body))
    intro hb i env before result after run bounded headerBound
    apply entry_lowerRange t i b hb (fun d xb => advB_lowerBlock _ _ _ body)
      ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    exact (entry_lowerBlock (some ⟨depth, exit, .next hb t i⟩) [(x, i, org)] false body
      env before result after run bounded ⟨exitBound, headerBound⟩).1
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine EntryRun.bind (entry_lowerEachSource lc v) fun ov =>
      EntryRun.bind (entry_regrowOf lc _) fun regrow =>
      EntryRun.bind (entry_eachSampled lc _ _) fun sampled =>
      EntryRun.bind (entry_emitDef lc _) fun startAt =>
      entry_whenLive lc _ fun _ => ?_
    apply entry_header1 lc (.data (.int .i64)) startAt
      (tail := fun hb i => lowerEach regrow ov.1 sampled hb i (fun d xb => do
        let elem ← emitDef (.refElem ov.2 i)
        let ev ← eachElemValue x byRef elem
        lowerBlock (some ⟨d, xb, .next hb .i64 i⟩)
          ((x, ev, org) :: (match idx with | some j => [(j, i, org)] | none => [])) false body))
      (fun hb i => advB_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        AdvB.bind (advB_emitDef _) fun elem => AdvB.bind (advB_eachElemValue _ _ _) fun ev =>
          advB_lowerBlock _ _ _ body))
    intro hb i env before result after run bounded headerBound
    apply entry_lowerEach regrow ov.1 sampled hb i
      (fun d xb => AdvB.bind (advB_emitDef _) fun elem =>
        AdvB.bind (advB_eachElemValue _ _ _) fun ev => advB_lowerBlock _ _ _ body)
      ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    apply And.left (b := LoopEntryTargets (some ⟨depth, exit, .next hb .i64 i⟩))
    apply (EntryRun.bind (entry_emitDef (some ⟨depth, exit, .next hb .i64 i⟩) _) fun elem =>
      EntryRun.bind (entry_eachElemValue (some ⟨depth, exit, .next hb .i64 i⟩) _ _ _) fun ev =>
        entry_lowerBlock (some ⟨depth, exit, .next hb .i64 i⟩) _ _ body)
      env before result after run bounded ⟨exitBound, headerBound⟩
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact EntryRun.bind (entry_lowerExpr lc e) fun v => EntryRun.bind (entry_coerceResult lc v org) fun _ =>
        EntryRun.bind (entry_pure lc _) fun _ => EntryRun.bind (entry_leaveTo lc 0) fun _ => entry_emitTerm lc _ (by simp [Term.successors])
    | none =>
      simp only [lowerStmt]
      exact EntryRun.bind (entry_pure lc _) fun _ => EntryRun.bind (entry_leaveTo lc 0) fun _ => entry_emitTerm lc _ (by simp [Term.successors])
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact entry_pure none _
    | some l =>
      simp only [lowerStmt]
      apply EntryRun.bind (entry_leaveTo (some l) _) fun _ => ?_
      apply entry_emitTerm (some l) _
      intro state targets target member
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      exact targets.1
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact entry_pure none _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        apply EntryRun.bind (entry_leaveTo (some l) _) fun _ => ?_
        apply entry_emitTerm (some l) _
        intro state targets target member
        simp only [Term.successors, List.mem_singleton] at member
        subst target
        simpa [LoopEntryTargets, hk] using targets.2
      | next h t i =>
        simp only [lowerStmt, hk]
        apply EntryRun.bind (entry_leaveTo (some l) _) fun _ => ?_
        apply EntryRun.bind (entry_emitDef (some l) _) fun _ => ?_
        apply entry_emitTerm (some l) _
        intro state targets target member
        simp only [Term.successors, List.mem_singleton] at member
        subst target
        simpa [LoopEntryTargets, hk] using targets.2
  | .print args org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerPrintArgs lc args) fun _ => entry_emitEffect lc _
  | .assertS e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerExpr lc e) fun cv => entry_assert_core lc cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact entry_emitTerm lc _ (by simp [Term.successors])
  | .exit e org => by
    simp only [lowerStmt]
    exact EntryRun.bind (entry_lowerExpr lc e) fun _ => entry_emitTerm lc _ (by simp [Term.successors])

end

end Goose.Lower.Validation
