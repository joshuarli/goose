import Goose.Lower.GeneratedTargetFramesLoops

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

set_option maxHeartbeats 5000000

mutual

theorem generatedTargetFrame_lowerExpr (lc : Option LoopCtx) : ∀ e : Expr, GeneratedTargetFrameRun lc (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExprs lc es) fun _ => generatedTargetFrame_emitDef lc _
  | .lit t n => by simp only [lowerExpr]; exact generatedTargetFrame_emitDef lc _
  | .bool b => by simp only [lowerExpr]; exact generatedTargetFrame_emitDef lc _
  | .read p => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun address =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc (.load address)) fun value =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_recordReadValueRootRecipe lc value p) fun _ =>
      generatedTargetFrame_pure lc value
  | .ref m p => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun r => generatedTargetFrame_borrowTo lc m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerView lc v) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBound lc lo) fun _ =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBound lc hi) fun _ => generatedTargetFrame_emitDef lc _
  | .len v => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerView lc v) fun _ => generatedTargetFrame_emitDef lc _
  | .un op e org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun a => GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf lc a) fun _ => generatedTargetFrame_emitDef lc _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc a) fun x => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc b) fun y =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf lc x) fun _ => generatedTargetFrame_emitDef lc _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc a) fun x => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc b) fun y =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy lc x) fun t => ?_
    cases t with
    | data t => cases t <;> exact generatedTargetFrame_emitDef lc _
    | view _ _ => exact generatedTargetFrame_emitDef lc _
  | .and a b => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc a) fun x => generatedTargetFrame_shortCircuit lc true x (generatedTargetFrame_lowerExpr lc b)
  | .or a b => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc a) fun x => generatedTargetFrame_shortCircuit lc false x (generatedTargetFrame_lowerExpr lc b)
  | .not e => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_emitDef lc _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun a => GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf lc a) fun _ => generatedTargetFrame_emitDef lc _
  | .call c args org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerArgs lc args) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun r => GeneratedTargetFrameRun.bind (generatedTargetFrame_read lc) fun le => by
        cases hnr : le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact generatedTargetFrame_pure lc _ | exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitTerm lc _ (by simp [Term.successors])) fun _ => generatedTargetFrame_pure lc _
  | .push owner e org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun v =>
      generatedTargetFrame_emitDef lc (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun _ => generatedTargetFrame_emitDef lc _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc c) fun cv =>
      generatedTargetFrame_ifE_recorded_core lc cv (sourceBlockScope t) ((generatedTargetFrame_lowerBlock none [] true t).withLoop (outer := lc)) ((generatedTargetFrame_lowerBlock none [] true f).withLoop (outer := lc))
  | .blockE b => by
    simp only [lowerExpr]
    exact (generatedTargetFrame_lowerBlock none [] true b).withLoop (outer := lc)
  | .arrLit t es => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExprs lc es) fun _ => generatedTargetFrame_emitDef lc _
  | .fill t e => by
    simp only [lowerExpr]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_emitDef lc _

theorem generatedTargetFrame_lowerExprs (lc : Option LoopCtx) : ∀ es : List Expr, GeneratedTargetFrameRun lc (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact generatedTargetFrame_pure lc _
  | e :: rest => by
    simp only [lowerExprs]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExprs lc rest) fun _ => generatedTargetFrame_pure lc _

theorem generatedTargetFrame_lowerArg (lc : Option LoopCtx) : ∀ a : Arg, GeneratedTargetFrameRun lc (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact generatedTargetFrame_lowerExpr lc e
  | .byRef m p => by
    simp only [lowerArg]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun r => generatedTargetFrame_borrowTo lc m r

theorem generatedTargetFrame_lowerArgs (lc : Option LoopCtx) : ∀ as : List Arg, GeneratedTargetFrameRun lc (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact generatedTargetFrame_pure lc _
  | a :: rest => by
    simp only [lowerArgs]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerArg lc a) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerArgs lc rest) fun _ => generatedTargetFrame_pure lc _

theorem generatedTargetFrame_lowerPlace (lc : Option LoopCtx) : ∀ p : Place, GeneratedTargetFrameRun lc (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun _ => generatedTargetFrame_emitDef lc _
  | .var x => by simp only [lowerPlace]; exact generatedTargetFrame_emitDef lc _
  | .global g => by simp only [lowerPlace]; exact generatedTargetFrame_emitDef lc _
  | .deref e => by simp only [lowerPlace]; exact generatedTargetFrame_lowerExpr lc e
  | .elem v i org => by
    simp only [lowerPlace]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerView lc v) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc i) fun _ => generatedTargetFrame_emitDef lc _

theorem generatedTargetFrame_lowerView (lc : Option LoopCtx) : ∀ v : View, GeneratedTargetFrameRun lc (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun _ => generatedTargetFrame_emitDef lc _
  | .val e => by
    simp only [lowerView]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_emitDef lc _

theorem generatedTargetFrame_lowerBound (lc : Option LoopCtx) : ∀ b : Bound, GeneratedTargetFrameRun lc (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact generatedTargetFrame_pure lc _
  | .expr e => by
    simp only [lowerBound]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_pure lc _
  | .fromEnd e => by
    simp only [lowerBound]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_pure lc _

theorem generatedTargetFrame_lowerEachSource (lc : Option LoopCtx) : ∀ v : View, GeneratedTargetFrameRun lc (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun _ => generatedTargetFrame_pure lc _
  | .val e => by
    simp only [lowerEachSource]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun _ => generatedTargetFrame_pure lc _

theorem generatedTargetFrame_lowerBlockValue (lc : Option LoopCtx) (want : Bool) : ∀ v : Option Expr, GeneratedTargetFrameRun lc (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact generatedTargetFrame_lowerExpr lc e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact generatedTargetFrame_pure lc _
    · simp only [lowerBlockValue, ↓reduceIte]; exact generatedTargetFrame_emitDef lc _

theorem generatedTargetFrame_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, GeneratedTargetFrameRun lc (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect lc _) fun _ => generatedTargetFrame_inScope sc
      (GeneratedTargetFrameRun.bind (generatedTargetFrame_initSlots lc _) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerStmts lc stmts) fun _ =>
        GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBlockValue lc want value) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect lc _) fun _ =>
        generatedTargetFrame_pure lc _)

theorem generatedTargetFrame_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, GeneratedTargetFrameRun lc (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact generatedTargetFrame_pure lc _
  | s :: rest => by
    simp only [lowerStmts]
    refine GeneratedTargetFrameRun.bind (generatedTargetFrame_isLive lc) fun live => ?_
    cases live
    · exact generatedTargetFrame_pure lc _
    · exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerStmt lc s) fun _ => generatedTargetFrame_lowerStmts lc rest

theorem generatedTargetFrame_lowerPrintArgs (lc : Option LoopCtx) : ∀ as : List PrintArg, GeneratedTargetFrameRun lc (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact generatedTargetFrame_pure lc _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPrintArgs lc rest) fun _ => generatedTargetFrame_pure lc _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPrintArgs lc rest) fun _ => generatedTargetFrame_pure lc _

theorem generatedTargetFrame_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, GeneratedTargetFrameRun lc (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun v =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_coerceSlot lc x v org) fun _ => generatedTargetFrame_emitEffect lc _
  | .assign p e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_emitEffect lc _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc p) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun _ =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf lc _) fun _ =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun _ => generatedTargetFrame_emitEffect lc _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun v =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_coerceSlot lc x v org) fun _ =>
        GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun _ => generatedTargetFrame_emitEffect lc _
  | .expr e _ => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun _ => generatedTargetFrame_pure lc _
  | .append owner src org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerView lc src) fun _ =>
      generatedTargetFrame_emitEffect lc _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc count) fun n =>
      generatedTargetFrame_emitEffect lc (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc size) fun n =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_pure lc _) fun fill => generatedTargetFrame_emitEffect lc (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r => GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc size) fun n =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc fill) fun v =>
        generatedTargetFrame_emitEffect lc (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r => generatedTargetFrame_emitEffect lc (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPlace lc owner) fun r =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect lc (.clear r (some org))) fun _ =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc replacement) fun run =>
        generatedTargetFrame_emitEffect lc (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc c) fun cv =>
        generatedTargetFrame_ifS_none_core lc cv
          (yes := do let _ ← lowerBlock lc [] false t; pure ())
          (GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBlock lc [] false t) fun _ =>
            generatedTargetFrame_pure lc ())
    | some fb =>
      simp only [lowerStmt]
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc c) fun cv =>
        generatedTargetFrame_ifS_some_core lc cv (generatedTargetFrame_lowerBlock lc [] false t) (generatedTargetFrame_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact generatedTargetFrame_header0 lc
      (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (by
        intro hb base env current after result baseCurrent frames terms headerFresh headerAt run
        exact generatedTargetFrame_lowerWhileFresh lc hb
          (generatedTargetFrame_lowerExpr none c)
          (fun depth exit => generatedTargetFrame_lowerBlock
            (some ⟨depth, exit, .jump hb⟩) [] false body)
          baseCurrent frames terms headerFresh headerAt run)
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc lo) fun a =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc hi) fun b =>
      generatedTargetFrame_whenLive lc _ fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf lc a) fun t => ?_
    exact generatedTargetFrame_header1 lc t a
      (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (by
        intro hb i base env current after result baseCurrent frames terms headerFresh headerAt eachRun
        exact generatedTargetFrame_lowerRangeFresh lc t i b hb
          (fun depth exit => generatedTargetFrame_lowerBlock
            (some ⟨depth, exit, .next hb t i⟩) [(x, i, org)] false body)
          baseCurrent frames terms headerFresh headerAt eachRun)
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerEachSource lc v) fun ov =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_regrowOf lc _) fun regrow =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_eachSampled lc _ _) fun sampled =>
      GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef lc _) fun startAt =>
      generatedTargetFrame_whenLive lc _ fun _ => ?_
    let eachBody (hb : BlockId) (i : ValueId) (depth : Nat) (exit : BlockId) : B ValueId := do
      let elem ← emitDef (.refElem ov.2 i)
      let ev ← eachElemValue x byRef elem
      lowerBlock (some ⟨depth, exit, .next hb .i64 i⟩)
        ((x, ev, org) :: (match idx with | some j => [(j, i, org)] | none => [])) false body
    exact generatedTargetFrame_header1 lc .i64 startAt
      (tail := fun hb i => lowerEach regrow ov.1 sampled hb i (eachBody hb i))
      (by
        intro hb i base env current after result baseCurrent frames terms headerFresh headerAt eachRun
        have bodyChecked : ∀ depth exit,
            GeneratedTargetFrameRun (some ⟨depth, exit, .next hb .i64 i⟩)
              (eachBody hb i depth exit) := by
          intro depth exit
          exact GeneratedTargetFrameRun.bind
            (generatedTargetFrame_emitDef (some ⟨depth, exit, .next hb .i64 i⟩) (.refElem ov.2 i)) fun elem =>
            GeneratedTargetFrameRun.bind
              (generatedTargetFrame_eachElemValue (some ⟨depth, exit, .next hb .i64 i⟩) x byRef elem) fun ev =>
              generatedTargetFrame_lowerBlock (some ⟨depth, exit, .next hb .i64 i⟩)
                ((x, ev, org) :: (match idx with | some j => [(j, i, org)] | none => [])) false body
        exact generatedTargetFrame_lowerEachFresh lc regrow ov.1 sampled hb i
          (body := eachBody hb i) bodyChecked baseCurrent frames terms headerFresh headerAt (by simpa [eachBody] using eachRun))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun v => GeneratedTargetFrameRun.bind (generatedTargetFrame_coerceResult lc v org) fun _ =>
        GeneratedTargetFrameRun.bind (generatedTargetFrame_pure lc _) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_leaveTo lc 0) fun _ => generatedTargetFrame_emitTerm lc _ (by simp [Term.successors])
    | none =>
      simp only [lowerStmt]
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_pure lc _) fun _ => GeneratedTargetFrameRun.bind (generatedTargetFrame_leaveTo lc 0) fun _ => generatedTargetFrame_emitTerm lc _ (by simp [Term.successors])
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact generatedTargetFrame_pure none _
    | some l =>
      simp only [lowerStmt]
      apply GeneratedTargetFrameRun.bind (generatedTargetFrame_leaveTo (some l) _) fun _ => ?_
      apply generatedTargetFrame_emitTerm (some l) _
      intro base target successor targetBound
      simp only [Term.successors, List.mem_singleton] at successor
      subst target
      exact Or.inl rfl
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact generatedTargetFrame_pure none _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        apply GeneratedTargetFrameRun.bind (generatedTargetFrame_leaveTo (some l) _) fun _ => ?_
        apply generatedTargetFrame_emitTerm (some l) _
        intro base target successor targetBound
        simp only [Term.successors, List.mem_singleton] at successor
        subst target
        simp only [LoopBuilderFrameTarget, hk]
        exact Or.inr True.intro
      | next h t i =>
        simp only [lowerStmt, hk]
        apply GeneratedTargetFrameRun.bind (generatedTargetFrame_leaveTo (some l) _) fun _ => ?_
        apply GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef (some l) _) fun _ => ?_
        apply generatedTargetFrame_emitTerm (some l) _
        intro base target successor targetBound
        simp only [Term.successors, List.mem_singleton] at successor
        subst target
        simp only [LoopBuilderFrameTarget, hk]
        exact Or.inr True.intro
  | .print args org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerPrintArgs lc args) fun _ => generatedTargetFrame_emitEffect lc _
  | .assertS e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun cv => generatedTargetFrame_assert_core lc cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact generatedTargetFrame_emitNoSuccessors lc (.abort .userAbort (some org)) rfl
  | .exit e org => by
    simp only [lowerStmt]
    exact GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerExpr lc e) fun value =>
      generatedTargetFrame_emitNoSuccessors lc (.exit value (some org)) rfl

end

end Goose.Lower
