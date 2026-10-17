import Goose.Lower.Validation.CfgPathActions


namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem path_lowerExpr : ∀ expr : Expr, PathAction (lowerExpr expr)
  | .structLit _ es => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExprs es) fun _ => path_emitDef _
  | .lit _ _ => path_emitDef _
  | .bool _ => path_emitDef _
  | .read place => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerPlace place) fun _ => path_emitDef _
  | .ref mu place => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerPlace place) fun value => path_borrowTo mu value
  | .slice _ view lo hi _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerView view) fun _ => PathAction.bind (path_lowerBound lo) fun _ =>
      PathAction.bind (path_lowerBound hi) fun _ => path_emitDef _
  | .len view => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerView view) fun _ => path_emitDef _
  | .un _ expr _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr expr) fun value => PathAction.bind (path_intTyOf value) fun _ => path_emitDef _
  | .bin _ left right _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr left) fun value => PathAction.bind (path_lowerExpr right) fun _ =>
      PathAction.bind (path_intTyOf value) fun _ => path_emitDef _
  | .cmp _ left right => by
    simp only [lowerExpr]
    refine PathAction.bind (path_lowerExpr left) fun value => PathAction.bind (path_lowerExpr right) fun _ =>
      PathAction.bind (path_valTy value) fun ty => ?_
    cases ty with
    | data ty => cases ty <;> exact path_emitDef _
    | view _ _ => exact path_emitDef _
  | .and left right => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr left) fun value =>
      ⟨advB_shortCircuit true value (path_lowerExpr right).advance,
        paths_shortCircuit true value (path_lowerExpr right).paths⟩
  | .or left right => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr left) fun value =>
      ⟨advB_shortCircuit false value (path_lowerExpr right).advance,
        paths_shortCircuit false value (path_lowerExpr right).paths⟩
  | .not expr => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr expr) fun _ => path_emitDef _
  | .conv _ _ expr _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr expr) fun value => PathAction.bind (path_intTyOf value) fun _ => path_emitDef _
  | .call context args _ => by
    simp only [lowerExpr]
    refine PathAction.bind (path_lowerArgs args) fun _ =>
      PathAction.bind (path_emitDef _) fun _ => PathAction.bind path_read fun env => ?_
    cases env.mod.noReturn context <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact PathAction.pure _ | exact PathAction.bind (path_emitTerm _) fun _ => PathAction.pure _
  | .push owner expr _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_lowerExpr expr) fun _ => path_emitDef _
  | .pop owner _ => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerPlace owner) fun _ => path_emitDef _
  | .ifE condition yes no => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr condition) fun value =>
      ⟨advB_ifE_core value (path_lowerBlock none [] true yes).advance (path_lowerBlock none [] true no).advance,
        paths_ifE_core value (path_lowerBlock none [] true yes).advance (path_lowerBlock none [] true no).advance
          (path_lowerBlock none [] true yes).paths (path_lowerBlock none [] true no).paths⟩
  | .blockE block => path_lowerBlock none [] true block
  | .arrLit _ es => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExprs es) fun _ => path_emitDef _
  | .fill _ expr => by
    simp only [lowerExpr]
    exact PathAction.bind (path_lowerExpr expr) fun _ => path_emitDef _

theorem path_lowerExprs : ∀ exprs : List Expr, PathAction (lowerExprs exprs)
  | [] => PathAction.pure _
  | expr :: rest => by
    simp only [lowerExprs]
    exact PathAction.bind (path_lowerExpr expr) fun _ => PathAction.bind (path_lowerExprs rest) fun _ => PathAction.pure _

theorem path_lowerArg : ∀ arg : Arg, PathAction (lowerArg arg)
  | .byVal expr => path_lowerExpr expr
  | .byRef mu place => by
    simp only [lowerArg]
    exact PathAction.bind (path_lowerPlace place) fun value => path_borrowTo mu value

theorem path_lowerArgs : ∀ args : List Arg, PathAction (lowerArgs args)
  | [] => PathAction.pure _
  | arg :: rest => by
    simp only [lowerArgs]
    exact PathAction.bind (path_lowerArg arg) fun _ => PathAction.bind (path_lowerArgs rest) fun _ => PathAction.pure _

theorem path_lowerPlace : ∀ place : Place, PathAction (lowerPlace place)
  | .field owner _ => by
    simp only [lowerPlace]
    exact PathAction.bind (path_lowerPlace owner) fun _ => path_emitDef _
  | .var _ => path_emitDef _
  | .global _ => path_emitDef _
  | .deref expr => path_lowerExpr expr
  | .elem view index _ => by
    simp only [lowerPlace]
    exact PathAction.bind (path_lowerView view) fun _ => PathAction.bind (path_lowerExpr index) fun _ => path_emitDef _

theorem path_lowerView : ∀ view : View, PathAction (lowerView view)
  | .of place => by
    simp only [lowerView]
    exact PathAction.bind (path_lowerPlace place) fun _ => path_emitDef _
  | .val expr => by
    simp only [lowerView]
    exact PathAction.bind (path_lowerExpr expr) fun _ => path_emitDef _

theorem path_lowerBound : ∀ bound : Bound, PathAction (lowerBound bound)
  | .omitted => PathAction.pure _
  | .expr expr => by
    simp only [lowerBound]
    exact PathAction.bind (path_lowerExpr expr) fun _ => PathAction.pure _
  | .fromEnd expr => by
    simp only [lowerBound]
    exact PathAction.bind (path_lowerExpr expr) fun _ => PathAction.pure _

theorem path_lowerEachSource : ∀ view : View, PathAction (lowerEachSource view)
  | .of place => by
    simp only [lowerEachSource]
    exact PathAction.bind (path_lowerPlace place) fun _ => PathAction.bind (path_emitDef _) fun _ => PathAction.pure _
  | .val expr => by
    simp only [lowerEachSource]
    exact PathAction.bind (path_lowerExpr expr) fun _ => PathAction.bind (path_emitDef _) fun _ => PathAction.pure _

theorem path_lowerBlockValue (want : Bool) : ∀ value : Option Expr, PathAction (lowerBlockValue want value)
  | some expr => path_lowerExpr expr
  | none => by
    cases want
    · exact PathAction.pure _
    · exact path_emitDef _

theorem path_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ block : Core.Block, PathAction (lowerBlock context pre want block)
  | .mk scope stmts value => by
    simp only [lowerBlock]
    exact PathAction.bind (path_emitEffect _) fun _ => path_inScope scope
      (PathAction.bind (path_initSlots pre) fun _ => PathAction.bind (path_lowerStmts context stmts) fun _ =>
        PathAction.bind (path_lowerBlockValue want value) fun _ =>
        PathAction.bind (path_emitEffect _) fun _ => PathAction.pure _)

theorem path_lowerStmts (context : Option LoopCtx) : ∀ stmts : List Stmt, PathAction (lowerStmts context stmts)
  | [] => PathAction.pure _
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
      have middlePaths := path_lowerStmt context stmt env before _ middle stmtRun paths bounded (by simp [current])
      have middleBound := liveBound_of_adv (advB_lowerStmt context stmt env before _ middle stmtRun) bounded
      exact (path_lowerStmts context rest).paths env middle result after restRun middlePaths middleBound

theorem path_lowerPrintArgs : ∀ args : List PrintArg, PathAction (lowerPrintArgs args)
  | [] => PathAction.pure _
  | .text _ :: rest => by
    simp only [lowerPrintArgs]
    exact PathAction.bind (path_lowerPrintArgs rest) fun _ => PathAction.pure _
  | .expr expr :: rest => by
    simp only [lowerPrintArgs]
    exact PathAction.bind (path_lowerExpr expr) fun _ => PathAction.bind (path_lowerPrintArgs rest) fun _ => PathAction.pure _

theorem path_lowerStmt (context : Option LoopCtx) : ∀ stmt : Stmt, LivePathRun (lowerStmt context stmt)
  | .letS var expr origin => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerExpr expr) fun value => PathAction.bind (path_coerceSlot var value origin) fun _ =>
      path_emitEffect _).live
  | .assign place expr _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace place) fun _ => PathAction.bind (path_lowerExpr expr) fun _ =>
      path_emitEffect _).live
  | .assignOp _ place expr _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace place) fun _ => PathAction.bind (path_emitDef _) fun old =>
      PathAction.bind (path_lowerExpr expr) fun _ => PathAction.bind (path_intTyOf old) fun _ =>
      PathAction.bind (path_emitDef _) fun _ => path_emitEffect _).live
  | .rebind var expr origin => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerExpr expr) fun value => PathAction.bind (path_coerceSlot var value origin) fun _ =>
      PathAction.bind (path_emitDef _) fun _ => path_emitEffect _).live
  | .expr expr _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerExpr expr) fun _ => PathAction.pure _).live
  | .append owner view _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_lowerView view) fun _ =>
      path_emitEffect _).live
  | .popN owner count _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_lowerExpr count) fun _ =>
      path_emitEffect _).live
  | .resize owner size fill _ => by
    cases fill with
    | none =>
      simp only [lowerStmt]
      exact (PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_lowerExpr size) fun _ =>
        PathAction.bind (PathAction.pure _) fun _ => path_emitEffect _).live
    | some expr =>
      simp only [lowerStmt]
      exact (PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_lowerExpr size) fun _ =>
        PathAction.bind (path_lowerExpr expr) fun _ => PathAction.bind (PathAction.pure _) fun _ => path_emitEffect _).live
  | .clear owner _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace owner) fun _ => path_emitEffect _).live
  | .assignWhole owner expr _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPlace owner) fun _ => PathAction.bind (path_emitEffect _) fun _ =>
      PathAction.bind (path_lowerExpr expr) fun _ => path_emitEffect _).live
  | .ifS condition yes no _ => by
    cases no with
    | none =>
      simp only [lowerStmt]
      exact (PathAction.bind (path_lowerExpr condition) fun value =>
        ⟨advB_ifS_none_core value (path_lowerBlock context [] false yes).advance,
          paths_ifS_none_core value (path_lowerBlock context [] false yes).paths⟩).live
    | some no =>
      simp only [lowerStmt]
      exact (PathAction.bind (path_lowerExpr condition) fun value =>
        ⟨advB_ifS_some_core value (path_lowerBlock context [] false yes).advance
            (path_lowerBlock context [] false no).advance,
          paths_ifS_some_core value (path_lowerBlock context [] false yes).advance (path_lowerBlock context [] false no).advance
            (path_lowerBlock context [] false yes).paths (path_lowerBlock context [] false no).paths⟩).live
  | .while condition body _ => by
    simp only [lowerStmt]
    exact paths_header0 (tail := fun header => lowerWhile header (lowerExpr condition)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) fun header =>
      LivePathRun.of_bounded (paths_lowerWhile header (condition := lowerExpr condition)
        (body := fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
        (path_lowerExpr condition).advance (path_lowerExpr condition).paths
        (fun depth exit => (path_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body).advance)
        (fun depth exit => (path_lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body).paths))
  | .forRange var lo hi body origin => by
    simp only [lowerStmt]
    refine (PathAction.bind (path_lowerExpr lo) fun first => PathAction.bind (path_lowerExpr hi) fun limit => ?_).live
    refine path_whenLive () (action := do
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
          (fun depth exit => (path_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body).advance)
    · refine LivePathRun.bind (advB_intTyOf first) (path_intTyOf first).paths
        (fun env state => congrArg LS.cur (intTyOf_eq (v := first) (le := env) (ls := state) rfl)) fun ty => ?_
      exact paths_header1 (.data (.int ty)) first
        (tail := fun header counter => lowerRange ty counter limit header (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(var, counter, origin)] false body))
        fun header counter => paths_lowerRange ty counter limit header
          (body := fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body)
          (fun depth exit => (path_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body).advance)
          (fun depth exit => (path_lowerBlock (some ⟨depth, exit, .next header ty counter⟩)
            [(var, counter, origin)] false body).paths)
  | .forEach var none view byRef body origin => by
    simp only [lowerStmt]
    refine (PathAction.bind (path_lowerEachSource view) fun pair =>
      PathAction.bind (path_regrowOf pair.1) fun regrow => PathAction.bind (path_eachSampled regrow pair.2) fun sampled =>
      PathAction.bind (path_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), PathAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: []
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact PathAction.bind (path_emitDef (.refElem pair.2 counter)) fun elem => PathAction.bind (path_eachElemValue var byRef elem) fun value =>
        path_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: []) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: []
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change PathAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine path_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) ?_ ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact paths_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => paths_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)
          (fun depth exit => (bodyPath header counter depth exit).paths)
  | .forEach var (some index) view byRef body origin => by
    simp only [lowerStmt]
    refine (PathAction.bind (path_lowerEachSource view) fun pair =>
      PathAction.bind (path_regrowOf pair.1) fun regrow => PathAction.bind (path_eachSampled regrow pair.2) fun sampled =>
      PathAction.bind (path_emitDef (.constInt .i64 0)) fun start => ?_).live
    have bodyPath : ∀ (header : BlockId) (counter : ValueId) (depth : Nat) (exit : BlockId), PathAction (do
        let elem ← emitDef (.refElem pair.2 counter)
        let value ← eachElemValue var byRef elem
        let pre := (var, value, origin) :: [(index, counter, origin)]
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body) := by
      intro header counter depth exit
      exact PathAction.bind (path_emitDef (.refElem pair.2 counter)) fun elem => PathAction.bind (path_eachElemValue var byRef elem) fun value =>
        path_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((var, value, origin) :: [(index, counter, origin)]) false body
    let eachBody : BlockId → ValueId → Nat → BlockId → B ValueId := fun header counter depth exit => do
      let elem ← emitDef (.refElem pair.2 counter)
      let value ← eachElemValue var byRef elem
      let pre := (var, value, origin) :: [(index, counter, origin)]
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) pre false body
    change PathAction (whenLive () fun _ => do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter))
    refine path_whenLive () (action := do
      let (header, params) ← newBlock [.data (.int .i64)]
      let counter := params.headD 0
      emitTerm (.br header [start])
      setCur (some header)
      lowerEach regrow pair.1 sampled header counter (eachBody header counter)) ?_ ?_
    · exact advB_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => advB_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter) (fun depth exit => (bodyPath header counter depth exit).advance)
    · exact paths_header1 (.data (.int .i64)) start
        (tail := fun header counter => lowerEach regrow pair.1 sampled header counter (eachBody header counter))
        fun header counter => paths_lowerEach regrow pair.1 sampled header counter
          (body := eachBody header counter)
          (fun depth exit => (bodyPath header counter depth exit).advance)
          (fun depth exit => (bodyPath header counter depth exit).paths)
  | .ret value origin => by
    cases value with
    | none =>
      simp only [lowerStmt]
      exact (PathAction.bind (PathAction.pure _) fun _ =>
        PathAction.bind (path_leaveTo _) fun _ => path_emitTerm _).live
    | some expr =>
      simp only [lowerStmt]
      exact (PathAction.bind (path_lowerExpr expr) fun value =>
        PathAction.bind (path_coerceResult value origin) fun _ =>
        PathAction.bind (PathAction.pure _) fun _ => PathAction.bind (path_leaveTo _) fun _ => path_emitTerm _).live
  | .brk _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (PathAction.pure _).live
    | some loop => exact (PathAction.bind (path_leaveTo _) fun _ => path_emitTerm _).live
  | .cont _ => by
    simp only [lowerStmt]
    cases context with
    | none => exact (PathAction.pure _).live
    | some loop =>
      refine (PathAction.bind (path_leaveTo _) fun _ => ?_).live
      cases loop.cont with
      | jump header => exact path_emitTerm _
      | next header ty counter => exact PathAction.bind (path_emitDef _) fun _ => path_emitTerm _
  | .print args _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerPrintArgs args) fun _ => path_emitEffect _).live
  | .assertS expr origin => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerExpr expr) fun value => path_assert value origin).live
  | .abort _ _ => (path_emitTerm _).live
  | .exit expr _ => by
    simp only [lowerStmt]
    exact (PathAction.bind (path_lowerExpr expr) fun _ => path_emitTerm _).live

end

end Goose.Lower.Validation
