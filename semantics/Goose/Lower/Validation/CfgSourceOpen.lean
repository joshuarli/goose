import Goose.Lower.Validation.CfgOpenActions


namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem open_lowerExpr : ∀ expr : Expr, OpenAction (lowerExpr expr)
  | .structLit _ es => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExprs es) fun _ => open_emitDef _
  | .lit _ _ => open_emitDef _
  | .bool _ => open_emitDef _
  | .read place => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerPlace place) fun _ => open_emitDef _
  | .ref mu place => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerPlace place) fun value => open_borrowTo mu value
  | .slice _ view lo hi _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerView view) fun _ => OpenAction.bind (open_lowerBound lo) fun _ =>
      OpenAction.bind (open_lowerBound hi) fun _ => open_emitDef _
  | .len view => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerView view) fun _ => open_emitDef _
  | .un _ expr _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr expr) fun value => OpenAction.bind (open_intTyOf value) fun _ => open_emitDef _
  | .bin _ left right _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr left) fun value => OpenAction.bind (open_lowerExpr right) fun _ =>
      OpenAction.bind (open_intTyOf value) fun _ => open_emitDef _
  | .cmp _ left right => by
    simp only [lowerExpr]
    refine OpenAction.bind (open_lowerExpr left) fun value => OpenAction.bind (open_lowerExpr right) fun _ =>
      OpenAction.bind (open_valTy value) fun ty => ?_
    cases ty with
    | data ty => cases ty <;> exact open_emitDef _
    | view _ _ => exact open_emitDef _
  | .and left right => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr left) fun value =>
      ⟨advB_shortCircuit true value (open_lowerExpr right).advance,
        opens_shortCircuit true value (open_lowerExpr right).advance⟩
  | .or left right => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr left) fun value =>
      ⟨advB_shortCircuit false value (open_lowerExpr right).advance,
        opens_shortCircuit false value (open_lowerExpr right).advance⟩
  | .not expr => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => open_emitDef _
  | .conv _ _ expr _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr expr) fun value => OpenAction.bind (open_intTyOf value) fun _ => open_emitDef _
  | .call context args _ => by
    simp only [lowerExpr]
    refine OpenAction.bind (open_lowerArgs args) fun _ =>
      OpenAction.bind (open_emitDef _) fun _ => OpenAction.bind open_read fun env => ?_
    cases env.mod.noReturn context <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact OpenAction.pure _ | exact OpenAction.bind (open_emitTerm _) fun _ => OpenAction.pure _
  | .push owner expr _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_lowerExpr expr) fun _ => open_emitDef _
  | .pop owner _ => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerPlace owner) fun _ => open_emitDef _
  | .ifE condition yes no => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr condition) fun value =>
      ⟨advB_ifE_core value (open_lowerBlock none [] true yes).advance (open_lowerBlock none [] true no).advance,
        opens_ifE_core value (open_lowerBlock none [] true yes).advance (open_lowerBlock none [] true no).advance⟩
  | .blockE block => open_lowerBlock none [] true block
  | .arrLit _ es => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExprs es) fun _ => open_emitDef _
  | .fill _ expr => by
    simp only [lowerExpr]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => open_emitDef _

theorem open_lowerExprs : ∀ exprs : List Expr, OpenAction (lowerExprs exprs)
  | [] => OpenAction.pure _
  | expr :: rest => by
    simp only [lowerExprs]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.bind (open_lowerExprs rest) fun _ => OpenAction.pure _

theorem open_lowerArg : ∀ arg : Arg, OpenAction (lowerArg arg)
  | .byVal expr => open_lowerExpr expr
  | .byRef mu place => by
    simp only [lowerArg]
    exact OpenAction.bind (open_lowerPlace place) fun value => open_borrowTo mu value

theorem open_lowerArgs : ∀ args : List Arg, OpenAction (lowerArgs args)
  | [] => OpenAction.pure _
  | arg :: rest => by
    simp only [lowerArgs]
    exact OpenAction.bind (open_lowerArg arg) fun _ => OpenAction.bind (open_lowerArgs rest) fun _ => OpenAction.pure _

theorem open_lowerPlace : ∀ place : Place, OpenAction (lowerPlace place)
  | .field owner _ => by
    simp only [lowerPlace]
    exact OpenAction.bind (open_lowerPlace owner) fun _ => open_emitDef _
  | .var _ => open_emitDef _
  | .global _ => open_emitDef _
  | .deref expr => open_lowerExpr expr
  | .elem view index _ => by
    simp only [lowerPlace]
    exact OpenAction.bind (open_lowerView view) fun _ => OpenAction.bind (open_lowerExpr index) fun _ => open_emitDef _

theorem open_lowerView : ∀ view : View, OpenAction (lowerView view)
  | .of place => by
    simp only [lowerView]
    exact OpenAction.bind (open_lowerPlace place) fun _ => open_emitDef _
  | .val expr => by
    simp only [lowerView]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => open_emitDef _

theorem open_lowerBound : ∀ bound : Bound, OpenAction (lowerBound bound)
  | .omitted => OpenAction.pure _
  | .expr expr => by
    simp only [lowerBound]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.pure _
  | .fromEnd expr => by
    simp only [lowerBound]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.pure _

theorem open_lowerEachSource : ∀ view : View, OpenAction (lowerEachSource view)
  | .of place => by
    simp only [lowerEachSource]
    exact OpenAction.bind (open_lowerPlace place) fun _ => OpenAction.bind (open_emitDef _) fun _ => OpenAction.pure _
  | .val expr => by
    simp only [lowerEachSource]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.bind (open_emitDef _) fun _ => OpenAction.pure _

theorem open_lowerBlockValue (want : Bool) : ∀ value : Option Expr, OpenAction (lowerBlockValue want value)
  | some expr => open_lowerExpr expr
  | none => by
    cases want
    · exact OpenAction.pure _
    · exact open_emitDef _

theorem open_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ block : Core.Block, OpenAction (lowerBlock context pre want block)
  | .mk scope stmts value => by
    simp only [lowerBlock]
    exact OpenAction.bind (open_emitEffect _) fun _ => open_inScope scope
      (OpenAction.bind (open_initSlots pre) fun _ => OpenAction.bind (open_lowerStmts context stmts) fun _ =>
        OpenAction.bind (open_lowerBlockValue want value) fun _ =>
        OpenAction.bind (open_emitEffect _) fun _ => OpenAction.pure _)

theorem open_lowerStmts (context : Option LoopCtx) : ∀ stmts : List Stmt, OpenAction (lowerStmts context stmts)
  | [] => OpenAction.pure _
  | stmt :: rest => by
    refine ⟨advB_lowerStmts context _, ?_⟩
    intro env before result after run paths bounded
    cases current : before.cur with
    | none =>
      simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact paths
    | some source =>
      simp only [lowerStmts] at run
      rw [bind_run, isLive_run current] at run
      simp only [ite_true] at run
      obtain ⟨_, middle, stmtRun, restRun⟩ := bind_eq.mp run
      have middlePaths := open_lowerStmt context stmt env before _ middle stmtRun paths bounded (by simp [current])
      have middleBound := liveBound_of_adv (advB_lowerStmt context stmt env before _ middle stmtRun) bounded
      exact (open_lowerStmts context rest).paths env middle result after restRun middlePaths middleBound

theorem open_lowerPrintArgs : ∀ args : List PrintArg, OpenAction (lowerPrintArgs args)
  | [] => OpenAction.pure _
  | .text _ :: rest => by
    simp only [lowerPrintArgs]
    exact OpenAction.bind (open_lowerPrintArgs rest) fun _ => OpenAction.pure _
  | .expr expr :: rest => by
    simp only [lowerPrintArgs]
    exact OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.bind (open_lowerPrintArgs rest) fun _ => OpenAction.pure _

theorem open_lowerStmt (context : Option LoopCtx) : ∀ stmt : Stmt, LiveOpenRun (lowerStmt context stmt)
  | .letS var expr origin => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerExpr expr) fun value => OpenAction.bind (open_coerceSlot var value origin) fun _ =>
      open_emitEffect _).live
  | .assign place expr _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace place) fun _ => OpenAction.bind (open_lowerExpr expr) fun _ =>
      open_emitEffect _).live
  | .assignOp _ place expr _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace place) fun _ => OpenAction.bind (open_emitDef _) fun old =>
      OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.bind (open_intTyOf old) fun _ =>
      OpenAction.bind (open_emitDef _) fun _ => open_emitEffect _).live
  | .rebind var expr origin => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerExpr expr) fun value => OpenAction.bind (open_coerceSlot var value origin) fun _ =>
      OpenAction.bind (open_emitDef _) fun _ => open_emitEffect _).live
  | .expr expr _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.pure _).live
  | .append owner view _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_lowerView view) fun _ =>
      open_emitEffect _).live
  | .popN owner count _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_lowerExpr count) fun _ =>
      open_emitEffect _).live
  | .resize owner size fill _ => by
    cases fill with
    | none =>
      simp only [lowerStmt]
      exact (OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_lowerExpr size) fun _ =>
        OpenAction.bind (OpenAction.pure _) fun _ => open_emitEffect _).live
    | some expr =>
      simp only [lowerStmt]
      exact (OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_lowerExpr size) fun _ =>
        OpenAction.bind (open_lowerExpr expr) fun _ => OpenAction.bind (OpenAction.pure _) fun _ => open_emitEffect _).live
  | .clear owner _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace owner) fun _ => open_emitEffect _).live
  | .assignWhole owner expr _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPlace owner) fun _ => OpenAction.bind (open_emitEffect _) fun _ =>
      OpenAction.bind (open_lowerExpr expr) fun _ => open_emitEffect _).live
  | .ifS condition yes no _ => by
    cases no with
    | none =>
      simp only [lowerStmt]
      exact (OpenAction.bind (open_lowerExpr condition) fun value =>
        ⟨advB_ifS_none_core value (open_lowerBlock context [] false yes).advance,
          opens_ifS_none_core value (open_lowerBlock context [] false yes).advance⟩).live
    | some no =>
      simp only [lowerStmt]
      exact (OpenAction.bind (open_lowerExpr condition) fun value =>
        ⟨advB_ifS_some_core value (open_lowerBlock context [] false yes).advance
            (open_lowerBlock context [] false no).advance,
          opens_ifS_some_core value (open_lowerBlock context [] false yes).advance (open_lowerBlock context [] false no).advance⟩).live
  | .while condition body _ => by
    simp only [lowerStmt]
    exact opens_header0 (tail := fun header => lowerWhile header (lowerExpr condition)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) fun header =>
      LiveOpenRun.of_bounded (opens_lowerWhile header (condition := lowerExpr condition)
        (body := fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
        (open_lowerExpr condition).advance (open_lowerExpr condition).paths
        (fun depth exit => (open_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body).advance))
  | .forRange var lo hi body origin => by
    simp only [lowerStmt]
    refine (OpenAction.bind (open_lowerExpr lo) fun first => OpenAction.bind (open_lowerExpr hi) fun limit => ?_).live
    refine open_whenLive () (action := do
      let ty ← intTyOf first
      let (header, params) ← newBlock [.data (.int ty)]
      let counter := params.headD 0
      emitTerm (.br header [first])
      setCur (some header)
      lowerRange ty counter limit header (fun depth exit =>
        lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body)) ?_ ?_
    · exact AdvB.bind (advB_intTyOf first) fun ty => advB_header1 (.data (.int ty)) first
        (tail := fun header counter => lowerRange ty counter limit header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body))
        fun header counter => advB_lowerRange ty counter limit header
          (fun depth exit => (open_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
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

  | .forEach var none view byRef body origin => by
    simp only [lowerStmt]
    refine (OpenAction.bind (open_lowerEachSource view) fun pair =>
      OpenAction.bind (open_regrowOf pair.1) fun regrow => OpenAction.bind (open_eachSampled regrow pair.2) fun sampled =>
      OpenAction.bind (open_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), OpenAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: []
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact OpenAction.bind (open_emitDef (.refElem pair.2 counter)) fun elem => OpenAction.bind (open_eachElemValue var byRef elem) fun value =>
        open_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: []) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: []
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change OpenAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine open_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) ?_ ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact opens_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => opens_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)

  | .forEach var (some index) view byRef body origin => by
    simp only [lowerStmt]
    refine (OpenAction.bind (open_lowerEachSource view) fun pair =>
      OpenAction.bind (open_regrowOf pair.1) fun regrow => OpenAction.bind (open_eachSampled regrow pair.2) fun sampled =>
      OpenAction.bind (open_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), OpenAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: [(index, counter, origin)]
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact OpenAction.bind (open_emitDef (.refElem pair.2 counter)) fun elem => OpenAction.bind (open_eachElemValue var byRef elem) fun value =>
        open_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: [(index, counter, origin)]) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: [(index, counter, origin)]
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change OpenAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine open_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) ?_ ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact opens_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => opens_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)

  | .ret value origin => by
    cases value with
    | none =>
      simp only [lowerStmt]
      exact (OpenAction.bind (OpenAction.pure _) fun _ =>
        OpenAction.bind (open_leaveTo _) fun _ => open_emitTerm _).live
    | some expr =>
      simp only [lowerStmt]
      exact (OpenAction.bind (open_lowerExpr expr) fun value =>
        OpenAction.bind (open_coerceResult value origin) fun _ =>
        OpenAction.bind (OpenAction.pure _) fun _ => OpenAction.bind (open_leaveTo _) fun _ => open_emitTerm _).live
  | .brk _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (OpenAction.pure _).live
    | some loop => exact (OpenAction.bind (open_leaveTo _) fun _ => open_emitTerm _).live
  | .cont _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (OpenAction.pure _).live
    | some loop =>
      refine (OpenAction.bind (open_leaveTo _) fun _ => ?_).live
      cases loop.cont with
      | jump header => exact open_emitTerm _
      | next header ty counter => exact OpenAction.bind (open_emitDef _) fun _ => open_emitTerm _
  | .print args _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerPrintArgs args) fun _ => open_emitEffect _).live
  | .assertS expr origin => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerExpr expr) fun value => open_assert value origin).live
  | .abort _ _ => (open_emitTerm _).live
  | .exit expr _ => by
    simp only [lowerStmt]
    exact (OpenAction.bind (open_lowerExpr expr) fun _ => open_emitTerm _).live

end

end Goose.Lower.Validation
