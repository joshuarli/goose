import Goose.Lower.GeneratedTargetsLoops

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

mutual

theorem generatedTargets_lowerExpr (lc : Option LoopCtx) : ∀ e : Expr, GeneratedTargetRun lc (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExprs lc es) fun _ => generatedTargets_emitDef lc _
  | .lit t n => by simp only [lowerExpr]; exact generatedTargets_emitDef lc _
  | .bool b => by simp only [lowerExpr]; exact generatedTargets_emitDef lc _
  | .read p => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun address =>
      GeneratedTargetRun.bind (generatedTargets_emitDef lc (.load address)) fun value =>
      GeneratedTargetRun.bind (generatedTargets_recordReadValueRootRecipe lc value p) fun _ =>
      generatedTargets_pure lc value
  | .ref m p => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun r => generatedTargets_borrowTo lc m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerView lc v) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerBound lc lo) fun _ =>
      GeneratedTargetRun.bind (generatedTargets_lowerBound lc hi) fun _ => generatedTargets_emitDef lc _
  | .len v => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerView lc v) fun _ => generatedTargets_emitDef lc _
  | .un op e org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun a => GeneratedTargetRun.bind (generatedTargets_intTyOf lc a) fun _ => generatedTargets_emitDef lc _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc a) fun x => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc b) fun y =>
      GeneratedTargetRun.bind (generatedTargets_intTyOf lc x) fun _ => generatedTargets_emitDef lc _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine GeneratedTargetRun.bind (generatedTargets_lowerExpr lc a) fun x => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc b) fun y =>
      GeneratedTargetRun.bind (generatedTargets_valTy lc x) fun t => ?_
    cases t with
    | data t => cases t <;> exact generatedTargets_emitDef lc _
    | view _ _ => exact generatedTargets_emitDef lc _
  | .and a b => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc a) fun x => generatedTargets_shortCircuit lc true x (generatedTargets_lowerExpr lc b) (advB_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc a) fun x => generatedTargets_shortCircuit lc false x (generatedTargets_lowerExpr lc b) (advB_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_emitDef lc _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun a => GeneratedTargetRun.bind (generatedTargets_intTyOf lc a) fun _ => generatedTargets_emitDef lc _
  | .call c args org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerArgs lc args) fun _ => GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun r => GeneratedTargetRun.bind (generatedTargets_read lc) fun le => by
        cases hnr : le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact generatedTargets_pure lc _ | exact GeneratedTargetRun.bind (generatedTargets_emitTerm lc _ (by simp [Term.successors])) fun _ => generatedTargets_pure lc _
  | .push owner e org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun v =>
      generatedTargets_emitDef lc (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun _ => generatedTargets_emitDef lc _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc c) fun cv =>
      generatedTargets_ifE_recorded_core lc cv (sourceBlockScope t) ((generatedTargets_lowerBlock none [] true t).withLoop (advB_lowerBlock none [] true t) lc) ((generatedTargets_lowerBlock none [] true f).withLoop (advB_lowerBlock none [] true f) lc)
  | .blockE b => by
    simp only [lowerExpr]
    exact (generatedTargets_lowerBlock none [] true b).withLoop (advB_lowerBlock none [] true b) lc
  | .arrLit t es => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExprs lc es) fun _ => generatedTargets_emitDef lc _
  | .fill t e => by
    simp only [lowerExpr]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_emitDef lc _

theorem generatedTargets_lowerExprs (lc : Option LoopCtx) : ∀ es : List Expr, GeneratedTargetRun lc (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact generatedTargets_pure lc _
  | e :: rest => by
    simp only [lowerExprs]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerExprs lc rest) fun _ => generatedTargets_pure lc _

theorem generatedTargets_lowerArg (lc : Option LoopCtx) : ∀ a : Arg, GeneratedTargetRun lc (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact generatedTargets_lowerExpr lc e
  | .byRef m p => by
    simp only [lowerArg]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun r => generatedTargets_borrowTo lc m r

theorem generatedTargets_lowerArgs (lc : Option LoopCtx) : ∀ as : List Arg, GeneratedTargetRun lc (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact generatedTargets_pure lc _
  | a :: rest => by
    simp only [lowerArgs]
    exact GeneratedTargetRun.bind (generatedTargets_lowerArg lc a) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerArgs lc rest) fun _ => generatedTargets_pure lc _

theorem generatedTargets_lowerPlace (lc : Option LoopCtx) : ∀ p : Place, GeneratedTargetRun lc (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun _ => generatedTargets_emitDef lc _
  | .var x => by simp only [lowerPlace]; exact generatedTargets_emitDef lc _
  | .global g => by simp only [lowerPlace]; exact generatedTargets_emitDef lc _
  | .deref e => by simp only [lowerPlace]; exact generatedTargets_lowerExpr lc e
  | .elem v i org => by
    simp only [lowerPlace]
    exact GeneratedTargetRun.bind (generatedTargets_lowerView lc v) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc i) fun _ => generatedTargets_emitDef lc _

theorem generatedTargets_lowerView (lc : Option LoopCtx) : ∀ v : View, GeneratedTargetRun lc (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun _ => generatedTargets_emitDef lc _
  | .val e => by
    simp only [lowerView]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_emitDef lc _

theorem generatedTargets_lowerBound (lc : Option LoopCtx) : ∀ b : Bound, GeneratedTargetRun lc (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact generatedTargets_pure lc _
  | .expr e => by
    simp only [lowerBound]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_pure lc _
  | .fromEnd e => by
    simp only [lowerBound]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_pure lc _

theorem generatedTargets_lowerEachSource (lc : Option LoopCtx) : ∀ v : View, GeneratedTargetRun lc (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun _ => GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun _ => generatedTargets_pure lc _
  | .val e => by
    simp only [lowerEachSource]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun _ => generatedTargets_pure lc _

theorem generatedTargets_lowerBlockValue (lc : Option LoopCtx) (want : Bool) : ∀ v : Option Expr, GeneratedTargetRun lc (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact generatedTargets_lowerExpr lc e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact generatedTargets_pure lc _
    · simp only [lowerBlockValue, ↓reduceIte]; exact generatedTargets_emitDef lc _

theorem generatedTargets_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, GeneratedTargetRun lc (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact GeneratedTargetRun.bind (generatedTargets_emitEffect lc _) fun _ => generatedTargets_inScope sc
      (GeneratedTargetRun.bind (generatedTargets_initSlots lc _) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerStmts lc stmts) fun _ =>
        GeneratedTargetRun.bind (generatedTargets_lowerBlockValue lc want value) fun _ => GeneratedTargetRun.bind (generatedTargets_emitEffect lc _) fun _ =>
        generatedTargets_pure lc _)

theorem generatedTargets_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, GeneratedTargetRun lc (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact generatedTargets_pure lc _
  | s :: rest => by
    simp only [lowerStmts]
    refine GeneratedTargetRun.bind (generatedTargets_isLive lc) fun live => ?_
    cases live
    · exact generatedTargets_pure lc _
    · exact GeneratedTargetRun.bind (generatedTargets_lowerStmt lc s) fun _ => generatedTargets_lowerStmts lc rest

theorem generatedTargets_lowerPrintArgs (lc : Option LoopCtx) : ∀ as : List PrintArg, GeneratedTargetRun lc (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact generatedTargets_pure lc _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPrintArgs lc rest) fun _ => generatedTargets_pure lc _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerPrintArgs lc rest) fun _ => generatedTargets_pure lc _

theorem generatedTargets_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, GeneratedTargetRun lc (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun v =>
      GeneratedTargetRun.bind (generatedTargets_coerceSlot lc x v org) fun _ => generatedTargets_emitEffect lc _
  | .assign p e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_emitEffect lc _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc p) fun _ => GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun _ =>
      GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => GeneratedTargetRun.bind (generatedTargets_intTyOf lc _) fun _ =>
      GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun _ => generatedTargets_emitEffect lc _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun v =>
      GeneratedTargetRun.bind (generatedTargets_coerceSlot lc x v org) fun _ =>
        GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun _ => generatedTargets_emitEffect lc _
  | .expr e _ => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_pure lc _
  | .append owner src org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun _ => GeneratedTargetRun.bind (generatedTargets_lowerView lc src) fun _ =>
      generatedTargets_emitEffect lc _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc count) fun n =>
      generatedTargets_emitEffect lc (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc size) fun n =>
      GeneratedTargetRun.bind (generatedTargets_pure lc _) fun fill => generatedTargets_emitEffect lc (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r => GeneratedTargetRun.bind (generatedTargets_lowerExpr lc size) fun n =>
      GeneratedTargetRun.bind (generatedTargets_lowerExpr lc fill) fun v =>
        generatedTargets_emitEffect lc (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r => generatedTargets_emitEffect lc (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPlace lc owner) fun r =>
      GeneratedTargetRun.bind (generatedTargets_emitEffect lc (.clear r (some org))) fun _ =>
      GeneratedTargetRun.bind (generatedTargets_lowerExpr lc replacement) fun run =>
        generatedTargets_emitEffect lc (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc c) fun cv => generatedTargets_ifS_none_core lc cv (generatedTargets_lowerBlock lc [] false t) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc c) fun cv =>
        generatedTargets_ifS_some_core lc cv (generatedTargets_lowerBlock lc [] false t) (generatedTargets_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    apply generatedTargets_header0 lc
      (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => advB_lowerWhile hb (advB_lowerExpr c) (fun d xb => advB_lowerBlock _ _ _ body))
    intro hb env before result after run bounded headerBound
    apply generatedTargets_lowerWhile hb (generatedTargets_lowerExpr none c) (advB_lowerExpr c)
      (fun d xb => advB_lowerBlock _ _ _ body) ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    exact (generatedTargets_lowerBlock (some ⟨depth, exit, .jump hb⟩) [] false body
      env before result after run bounded ⟨exitBound, headerBound⟩).1
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine GeneratedTargetRun.bind (generatedTargets_lowerExpr lc lo) fun a =>
      GeneratedTargetRun.bind (generatedTargets_lowerExpr lc hi) fun b =>
      generatedTargets_whenLive lc _ fun _ => GeneratedTargetRun.bind (generatedTargets_intTyOf lc a) fun t => ?_
    apply generatedTargets_header1 lc (.data (.int t)) a
      (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => advB_lowerRange t i b hb (fun d xb => advB_lowerBlock _ _ _ body))
    intro hb i env before result after run bounded headerBound
    apply generatedTargets_lowerRange t i b hb (fun d xb => advB_lowerBlock _ _ _ body)
      ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    exact (generatedTargets_lowerBlock (some ⟨depth, exit, .next hb t i⟩) [(x, i, org)] false body
      env before result after run bounded ⟨exitBound, headerBound⟩).1
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine GeneratedTargetRun.bind (generatedTargets_lowerEachSource lc v) fun ov =>
      GeneratedTargetRun.bind (generatedTargets_regrowOf lc _) fun regrow =>
      GeneratedTargetRun.bind (generatedTargets_eachSampled lc _ _) fun sampled =>
      GeneratedTargetRun.bind (generatedTargets_emitDef lc _) fun startAt =>
      generatedTargets_whenLive lc _ fun _ => ?_
    apply generatedTargets_header1 lc (.data (.int .i64)) startAt
      (tail := fun hb i => lowerEach regrow ov.1 sampled hb i (fun d xb => do
        let elem ← emitDef (.refElem ov.2 i)
        let ev ← eachElemValue x byRef elem
        lowerBlock (some ⟨d, xb, .next hb .i64 i⟩)
          ((x, ev, org) :: (match idx with | some j => [(j, i, org)] | none => [])) false body))
      (fun hb i => advB_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        AdvB.bind (advB_emitDef _) fun elem => AdvB.bind (advB_eachElemValue _ _ _) fun ev =>
          advB_lowerBlock _ _ _ body))
    intro hb i env before result after run bounded headerBound
    apply generatedTargets_lowerEach regrow ov.1 sampled hb i
      (fun d xb => AdvB.bind (advB_emitDef _) fun elem =>
        AdvB.bind (advB_eachElemValue _ _ _) fun ev => advB_lowerBlock _ _ _ body)
      ?_ run bounded headerBound
    intro depth exit env before result after run bounded headerBound exitBound
    apply And.left (b := LoopBuilderTargets (some ⟨depth, exit, .next hb .i64 i⟩) after)
    apply (GeneratedTargetRun.bind (generatedTargets_emitDef (some ⟨depth, exit, .next hb .i64 i⟩) _) fun elem =>
      GeneratedTargetRun.bind (generatedTargets_eachElemValue (some ⟨depth, exit, .next hb .i64 i⟩) _ _ _) fun ev =>
        generatedTargets_lowerBlock (some ⟨depth, exit, .next hb .i64 i⟩) _ _ body)
      env before result after run bounded ⟨exitBound, headerBound⟩
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun v => GeneratedTargetRun.bind (generatedTargets_coerceResult lc v org) fun _ =>
        GeneratedTargetRun.bind (generatedTargets_pure lc _) fun _ => GeneratedTargetRun.bind (generatedTargets_leaveTo lc 0) fun _ => generatedTargets_emitTerm lc _ (by simp [Term.successors])
    | none =>
      simp only [lowerStmt]
      exact GeneratedTargetRun.bind (generatedTargets_pure lc _) fun _ => GeneratedTargetRun.bind (generatedTargets_leaveTo lc 0) fun _ => generatedTargets_emitTerm lc _ (by simp [Term.successors])
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact generatedTargets_pure none _
    | some l =>
      simp only [lowerStmt]
      apply GeneratedTargetRun.bind (generatedTargets_leaveTo (some l) _) fun _ => ?_
      apply generatedTargets_emitTerm (some l) _
      intro state targets target member
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      exact targets.1
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact generatedTargets_pure none _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        apply GeneratedTargetRun.bind (generatedTargets_leaveTo (some l) _) fun _ => ?_
        apply generatedTargets_emitTerm (some l) _
        intro state targets target member
        simp only [Term.successors, List.mem_singleton] at member
        subst target
        simpa [LoopBuilderTargets, hk] using targets.2
      | next h t i =>
        simp only [lowerStmt, hk]
        apply GeneratedTargetRun.bind (generatedTargets_leaveTo (some l) _) fun _ => ?_
        apply GeneratedTargetRun.bind (generatedTargets_emitDef (some l) _) fun _ => ?_
        apply generatedTargets_emitTerm (some l) _
        intro state targets target member
        simp only [Term.successors, List.mem_singleton] at member
        subst target
        simpa [LoopBuilderTargets, hk] using targets.2
  | .print args org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerPrintArgs lc args) fun _ => generatedTargets_emitEffect lc _
  | .assertS e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun cv => generatedTargets_assert_core lc cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact generatedTargets_emitTerm lc _ (by simp [Term.successors])
  | .exit e org => by
    simp only [lowerStmt]
    exact GeneratedTargetRun.bind (generatedTargets_lowerExpr lc e) fun _ => generatedTargets_emitTerm lc _ (by simp [Term.successors])

end

end Goose.Lower
