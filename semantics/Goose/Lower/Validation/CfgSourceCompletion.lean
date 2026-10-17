import Goose.Lower.Validation.CfgCompleteLoop
import Goose.Lower.Validation.CfgSourceOpen


namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem complete_lowerExpr : ∀ expr : Expr, CompletionAction (lowerExpr expr)
  | .structLit _ es => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExprs es) fun _ => complete_emitDef _
  | .lit _ _ => complete_emitDef _
  | .bool _ => complete_emitDef _
  | .read place => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerPlace place) fun _ => complete_emitDef _
  | .ref mu place => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerPlace place) fun value => complete_borrowTo mu value
  | .slice _ view lo hi _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerView view) fun _ => CompletionAction.bind (complete_lowerBound lo) fun _ =>
      CompletionAction.bind (complete_lowerBound hi) fun _ => complete_emitDef _
  | .len view => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerView view) fun _ => complete_emitDef _
  | .un _ expr _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr expr) fun value => CompletionAction.bind (complete_intTyOf value) fun _ => complete_emitDef _
  | .bin _ left right _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr left) fun value => CompletionAction.bind (complete_lowerExpr right) fun _ =>
      CompletionAction.bind (complete_intTyOf value) fun _ => complete_emitDef _
  | .cmp _ left right => by
    simp only [lowerExpr]
    refine CompletionAction.bind (complete_lowerExpr left) fun value => CompletionAction.bind (complete_lowerExpr right) fun _ =>
      CompletionAction.bind (complete_valTy value) fun ty => ?_
    cases ty with
    | data ty => cases ty <;> exact complete_emitDef _
    | view _ _ => exact complete_emitDef _
  | .and left right => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr left) fun value =>
      complete_shortCircuit true value (complete_lowerExpr right)
  | .or left right => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr left) fun value =>
      complete_shortCircuit false value (complete_lowerExpr right)
  | .not expr => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitDef _
  | .conv _ _ expr _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr expr) fun value => CompletionAction.bind (complete_intTyOf value) fun _ => complete_emitDef _
  | .call context args _ => by
    simp only [lowerExpr]
    refine CompletionAction.bind (complete_lowerArgs args) fun _ =>
      CompletionAction.bind (complete_emitDef _) fun _ => CompletionAction.bind complete_read fun env => ?_
    cases env.mod.noReturn context <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact CompletionAction.pure _ | exact CompletionAction.bind (complete_emitTerm _) fun _ => CompletionAction.pure _
  | .push owner expr _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitDef _
  | .pop owner _ => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerPlace owner) fun _ => complete_emitDef _
  | .ifE condition yes no => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr condition) fun value =>
      complete_ifE value (sourceBlockScope yes)
        (complete_lowerBlock none [] true yes) (complete_lowerBlock none [] true no)
  | .blockE block => complete_lowerBlock none [] true block
  | .arrLit _ es => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExprs es) fun _ => complete_emitDef _
  | .fill _ expr => by
    simp only [lowerExpr]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitDef _

theorem complete_lowerExprs : ∀ exprs : List Expr, CompletionAction (lowerExprs exprs)
  | [] => CompletionAction.pure _
  | expr :: rest => by
    simp only [lowerExprs]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.bind (complete_lowerExprs rest) fun _ => CompletionAction.pure _

theorem complete_lowerArg : ∀ arg : Arg, CompletionAction (lowerArg arg)
  | .byVal expr => complete_lowerExpr expr
  | .byRef mu place => by
    simp only [lowerArg]
    exact CompletionAction.bind (complete_lowerPlace place) fun value => complete_borrowTo mu value

theorem complete_lowerArgs : ∀ args : List Arg, CompletionAction (lowerArgs args)
  | [] => CompletionAction.pure _
  | arg :: rest => by
    simp only [lowerArgs]
    exact CompletionAction.bind (complete_lowerArg arg) fun _ => CompletionAction.bind (complete_lowerArgs rest) fun _ => CompletionAction.pure _

theorem complete_lowerPlace : ∀ place : Place, CompletionAction (lowerPlace place)
  | .field owner _ => by
    simp only [lowerPlace]
    exact CompletionAction.bind (complete_lowerPlace owner) fun _ => complete_emitDef _
  | .var _ => complete_emitDef _
  | .global _ => complete_emitDef _
  | .deref expr => complete_lowerExpr expr
  | .elem view index _ => by
    simp only [lowerPlace]
    exact CompletionAction.bind (complete_lowerView view) fun _ => CompletionAction.bind (complete_lowerExpr index) fun _ => complete_emitDef _

theorem complete_lowerView : ∀ view : View, CompletionAction (lowerView view)
  | .of place => by
    simp only [lowerView]
    exact CompletionAction.bind (complete_lowerPlace place) fun _ => complete_emitDef _
  | .val expr => by
    simp only [lowerView]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitDef _

theorem complete_lowerBound : ∀ bound : Bound, CompletionAction (lowerBound bound)
  | .omitted => CompletionAction.pure _
  | .expr expr => by
    simp only [lowerBound]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.pure _
  | .fromEnd expr => by
    simp only [lowerBound]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.pure _

theorem complete_lowerEachSource : ∀ view : View, CompletionAction (lowerEachSource view)
  | .of place => by
    simp only [lowerEachSource]
    exact CompletionAction.bind (complete_lowerPlace place) fun _ => CompletionAction.bind (complete_emitDef _) fun _ => CompletionAction.pure _
  | .val expr => by
    simp only [lowerEachSource]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.bind (complete_emitDef _) fun _ => CompletionAction.pure _

theorem complete_lowerBlockValue (want : Bool) : ∀ value : Option Expr, CompletionAction (lowerBlockValue want value)
  | some expr => complete_lowerExpr expr
  | none => by
    cases want
    · exact CompletionAction.pure _
    · exact complete_emitDef _

theorem complete_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ block : Core.Block, CompletionAction (lowerBlock context pre want block)
  | .mk scope stmts value => by
    simp only [lowerBlock]
    exact CompletionAction.bind (complete_emitEffect _) fun _ => complete_inScope scope
      (CompletionAction.bind (complete_initSlots pre) fun _ => CompletionAction.bind (complete_lowerStmts context stmts) fun _ =>
        CompletionAction.bind (complete_lowerBlockValue want value) fun _ =>
        CompletionAction.bind (complete_emitEffect _) fun _ => CompletionAction.pure _)

theorem complete_lowerStmts (context : Option LoopCtx) : ∀ stmts : List Stmt, CompletionAction (lowerStmts context stmts)
  | [] => CompletionAction.pure _
  | stmt :: rest => by
    refine ⟨open_lowerStmts context _, ?_⟩
    intro env before result after run openBefore shapedBefore
    cases current : before.cur with
    | none =>
      simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact ⟨shapedBefore, rfl⟩
    | some source =>
      simp only [lowerStmts] at run
      rw [bind_run, isLive_run current] at run
      simp only [ite_true] at run
      obtain ⟨_, middle, stmtRun, restRun⟩ := bind_eq.mp run
      obtain ⟨shapeMiddle, countStmt⟩ := complete_lowerStmt context stmt env before _ middle stmtRun
        openBefore shapedBefore (by simp [current])
      have openMiddle := open_lowerStmt context stmt env before _ middle stmtRun openBefore openBefore.bound (by simp [current])
      obtain ⟨shapeAfter, countRest⟩ := (complete_lowerStmts context rest).complete env middle result after restRun openMiddle shapeMiddle
      exact ⟨shapeAfter, by omega⟩

theorem complete_lowerPrintArgs : ∀ args : List PrintArg, CompletionAction (lowerPrintArgs args)
  | [] => CompletionAction.pure _
  | .text _ :: rest => by
    simp only [lowerPrintArgs]
    exact CompletionAction.bind (complete_lowerPrintArgs rest) fun _ => CompletionAction.pure _
  | .expr expr :: rest => by
    simp only [lowerPrintArgs]
    exact CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.bind (complete_lowerPrintArgs rest) fun _ => CompletionAction.pure _

theorem complete_lowerStmt (context : Option LoopCtx) : ∀ stmt : Stmt, LiveCompletionRun (lowerStmt context stmt)
  | .letS var expr origin => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerExpr expr) fun value => CompletionAction.bind (complete_coerceSlot var value origin) fun _ =>
      complete_emitEffect _).live
  | .assign place expr _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace place) fun _ => CompletionAction.bind (complete_lowerExpr expr) fun _ =>
      complete_emitEffect _).live
  | .assignOp _ place expr _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace place) fun _ => CompletionAction.bind (complete_emitDef _) fun old =>
      CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.bind (complete_intTyOf old) fun _ =>
      CompletionAction.bind (complete_emitDef _) fun _ => complete_emitEffect _).live
  | .rebind var expr origin => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerExpr expr) fun value => CompletionAction.bind (complete_coerceSlot var value origin) fun _ =>
      CompletionAction.bind (complete_emitDef _) fun _ => complete_emitEffect _).live
  | .expr expr _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.pure _).live
  | .append owner view _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_lowerView view) fun _ =>
      complete_emitEffect _).live
  | .popN owner count _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_lowerExpr count) fun _ =>
      complete_emitEffect _).live
  | .resize owner size fill _ => by
    cases fill with
    | none =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_lowerExpr size) fun _ =>
        CompletionAction.bind (CompletionAction.pure _) fun _ => complete_emitEffect _).live
    | some expr =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_lowerExpr size) fun _ =>
        CompletionAction.bind (complete_lowerExpr expr) fun _ => CompletionAction.bind (CompletionAction.pure _) fun _ => complete_emitEffect _).live
  | .clear owner _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => complete_emitEffect _).live
  | .assignWhole owner expr _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPlace owner) fun _ => CompletionAction.bind (complete_emitEffect _) fun _ =>
      CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitEffect _).live
  | .ifS condition yes no _ => by
    cases no with
    | none =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (complete_lowerExpr condition) fun value =>
        complete_ifS_none value (complete_lowerBlock context [] false yes)).live
    | some no =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (complete_lowerExpr condition) fun value =>
        complete_ifS_some value (complete_lowerBlock context [] false yes) (complete_lowerBlock context [] false no)).live
  | .while condition body _ => by
    simp only [lowerStmt]
    exact complete_header0 (tail := fun header => lowerWhile header (lowerExpr condition)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) fun header =>
      (complete_lowerWhile header (condition := lowerExpr condition)
        (body := fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
        (complete_lowerExpr condition)
        (fun depth exit => complete_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)).live
  | .forRange var lo hi body origin => by
    simp only [lowerStmt]
    refine (CompletionAction.bind (complete_lowerExpr lo) fun first => CompletionAction.bind (complete_lowerExpr hi) fun limit => ?_).live
    refine complete_whenLive () (action := do
      let ty ← intTyOf first
      let (header, params) ← newBlock [.data (.int ty)]
      let counter := params.headD 0
      emitTerm (.br header [first])
      setCur (some header)
      lowerRange ty counter limit header (fun depth exit =>
        lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body)) (open_whenLive () ?_ ?_) ?_
    · exact AdvB.bind (advB_intTyOf first) fun ty => advB_header1 (.data (.int ty)) first
        (tail := fun header counter => lowerRange ty counter limit header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body))
        fun header counter => advB_lowerRange ty counter limit header
          (fun depth exit => (complete_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body).advance)
    · refine LiveOpenRun.bind (advB_intTyOf first) (open_intTyOf first).paths
        (fun env state => congrArg LS.cur (intTyOf_eq (v := first) (le := env) (ls := state) rfl)) fun ty => ?_
      exact opens_header1 (.data (.int ty)) first
        (tail := fun header counter => lowerRange ty counter limit header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body))
        fun header counter => opens_lowerRange ty counter limit header
          (body := fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body)
          (fun depth exit => (open_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body).advance)

    · refine LiveCompletionRun.bind (complete_intTyOf first)
        (fun env state => congrArg LS.cur (intTyOf_eq (v := first) (le := env) (ls := state) rfl)) fun ty => ?_
      exact complete_header1 (.data (.int ty)) first
        (tail := fun header counter => lowerRange ty counter limit header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body))
        fun header counter => complete_lowerRange ty counter limit header
          (body := fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body)
          (fun depth exit => (complete_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body))

  | .forEach var none view byRef body origin => by
    simp only [lowerStmt]
    refine (CompletionAction.bind (complete_lowerEachSource view) fun pair =>
      CompletionAction.bind (complete_regrowOf pair.1) fun regrow => CompletionAction.bind (complete_eachSampled regrow pair.2) fun sampled =>
      CompletionAction.bind (complete_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), CompletionAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: []
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact CompletionAction.bind (complete_emitDef (.refElem pair.2 counter)) fun elem => CompletionAction.bind (complete_eachElemValue var byRef elem) fun value =>
        complete_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: []) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: []
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change CompletionAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine complete_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) (open_whenLive () ?_ ?_) ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact opens_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => opens_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact complete_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => complete_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => bodyPath header counter depth exit)

  | .forEach var (some index) view byRef body origin => by
    simp only [lowerStmt]
    refine (CompletionAction.bind (complete_lowerEachSource view) fun pair =>
      CompletionAction.bind (complete_regrowOf pair.1) fun regrow => CompletionAction.bind (complete_eachSampled regrow pair.2) fun sampled =>
      CompletionAction.bind (complete_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), CompletionAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: [(index, counter, origin)]
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact CompletionAction.bind (complete_emitDef (.refElem pair.2 counter)) fun elem => CompletionAction.bind (complete_eachElemValue var byRef elem) fun value =>
        complete_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: [(index, counter, origin)]) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: [(index, counter, origin)]
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change CompletionAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine complete_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) (open_whenLive () ?_ ?_) ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact opens_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => opens_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact complete_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => complete_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => bodyPath header counter depth exit)

  | .ret value origin => by
    cases value with
    | none =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (CompletionAction.pure _) fun _ =>
        CompletionAction.bind (complete_leaveTo _) fun _ => complete_emitTerm _).live
    | some expr =>
      simp only [lowerStmt]
      exact (CompletionAction.bind (complete_lowerExpr expr) fun value =>
        CompletionAction.bind (complete_coerceResult value origin) fun _ =>
        CompletionAction.bind (CompletionAction.pure _) fun _ => CompletionAction.bind (complete_leaveTo _) fun _ => complete_emitTerm _).live
  | .brk _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (CompletionAction.pure _).live
    | some loop => exact (CompletionAction.bind (complete_leaveTo _) fun _ => complete_emitTerm _).live
  | .cont _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (CompletionAction.pure _).live
    | some loop =>
      refine (CompletionAction.bind (complete_leaveTo _) fun _ => ?_).live
      cases loop.cont with
      | jump header => exact complete_emitTerm _
      | next header ty counter => exact CompletionAction.bind (complete_emitDef _) fun _ => complete_emitTerm _
  | .print args _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerPrintArgs args) fun _ => complete_emitEffect _).live
  | .assertS expr origin => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerExpr expr) fun value => complete_assert value origin).live
  | .abort _ _ => (complete_emitTerm _).live
  | .exit expr _ => by
    simp only [lowerStmt]
    exact (CompletionAction.bind (complete_lowerExpr expr) fun _ => complete_emitTerm _).live

end

end Goose.Lower.Validation
