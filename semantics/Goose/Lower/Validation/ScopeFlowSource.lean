import Goose.Lower.Validation.ScopeFlowLoop
import Goose.Lower.Validation.ScopeLexical

set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem scopeFlow_lowerExpr (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ expr : Expr, ScopeTableContains parents (exprScopes parent expr) →
      ScopeFlowAction parents parent loop (lowerExpr expr)
  | .structLit type exprs, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExprs parents parent loop exprs source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .lit type value, source => by
    simp only [lowerExpr]
    exact ScopeFlowAction.emitDef parents parent loop _
  | .bool value, source => by
    simp only [lowerExpr]
    exact ScopeFlowAction.emitDef parents parent loop _
  | .read place, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerPlace parents parent loop place source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .ref mutability place, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerPlace parents parent loop place source).bind fun value => ScopeFlowAction.freezeTo parents parent loop mutability value
  | .slice mutability view lower upper origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerView parents parent loop view source.1.1).bind fun _ =>
      (scopeFlow_lowerBound parents parent loop lower source.1.2).bind fun _ =>
      (scopeFlow_lowerBound parents parent loop upper source.2).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .len view, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerView parents parent loop view source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .un op expr origin, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun value =>
      (ScopeFlowAction.intTyOf parents parent loop value).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .bin op left right origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop left source.1).bind fun value =>
      (scopeFlow_lowerExpr parents parent loop right source.2).bind fun _ =>
      (ScopeFlowAction.intTyOf parents parent loop value).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .cmp op left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    refine (scopeFlow_lowerExpr parents parent loop left source.1).bind fun value =>
      (scopeFlow_lowerExpr parents parent loop right source.2).bind fun _ =>
      (ScopeFlowAction.valTy parents parent loop value).bind fun type => ?_
    cases type with
    | data type => cases type <;> exact ScopeFlowAction.emitDef parents parent loop _
    | view _ _ => exact ScopeFlowAction.emitDef parents parent loop _
  | .and left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop left source.1).bind fun value =>
      ScopeFlowAction.shortCircuit true value (scopeFlow_lowerExpr parents parent loop right source.2)
  | .or left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop left source.1).bind fun value =>
      ScopeFlowAction.shortCircuit false value (scopeFlow_lowerExpr parents parent loop right source.2)
  | .not expr, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .conv kind target expr origin, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun value =>
      (ScopeFlowAction.intTyOf parents parent loop value).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .call context args origin, source => by
    simp only [lowerExpr]
    refine (scopeFlow_lowerArgs parents parent loop args source).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun result =>
      (ScopeFlowAction.read parents parent loop).bind fun env => ?_
    cases noReturn : env.mod.noReturn context <;> simp only [Bool.false_eq_true, reduceIte]
    · exact ScopeFlowAction.pure parents parent loop _
    · exact (ScopeFlowAction.emptyTerm parents parent loop .unreachable rfl rfl).bind fun _ => ScopeFlowAction.pure parents parent loop result
  | .push owner expr origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop expr source.2).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .pop owner origin, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerPlace parents parent loop owner source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .ifE condition yes no, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop condition source.1.1).bind fun value =>
      ScopeFlowAction.ifValue value ((scopeFlow_lowerBlock parents parent none [] true yes source.1.2).weakenLoop loop)
        ((scopeFlow_lowerBlock parents parent none [] true no source.2).weakenLoop loop)
  | .blockE block, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerBlock parents parent none [] true block source).weakenLoop loop
  | .arrLit type exprs, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExprs parents parent loop exprs source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .fill type expr, source => by
    simp only [lowerExpr]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _

theorem scopeFlow_lowerExprs (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ exprs : List Expr, ScopeTableContains parents (exprsScopes parent exprs) →
      ScopeFlowAction parents parent loop (lowerExprs exprs)
  | [], source => ScopeFlowAction.pure parents parent loop _
  | expr :: rest, source => by
    simp only [exprsScopes, ScopeTableContains.append] at source
    simp only [lowerExprs]
    exact (scopeFlow_lowerExpr parents parent loop expr source.1).bind fun _ =>
      (scopeFlow_lowerExprs parents parent loop rest source.2).bind fun _ => ScopeFlowAction.pure parents parent loop _

theorem scopeFlow_lowerArg (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ arg : Arg, ScopeTableContains parents (argsScopes parent [arg]) →
      ScopeFlowAction parents parent loop (lowerArg arg)
  | .byVal expr, source => by
    simp only [argsScopes, List.append_nil] at source
    exact scopeFlow_lowerExpr parents parent loop expr source
  | .byRef mutability place, source => by
    simp only [argsScopes, List.append_nil] at source
    simp only [lowerArg]
    exact (scopeFlow_lowerPlace parents parent loop place source).bind fun value =>
      ScopeFlowAction.freezeTo parents parent loop mutability value

theorem scopeFlow_lowerArgs (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ args : List Arg, ScopeTableContains parents (argsScopes parent args) →
      ScopeFlowAction parents parent loop (lowerArgs args)
  | [], source => ScopeFlowAction.pure parents parent loop _
  | arg :: rest, source => by
    have split : argsScopes parent (arg :: rest) = argsScopes parent [arg] ++ argsScopes parent rest := by
      cases arg <;> simp [argsScopes]
    rw [split, ScopeTableContains.append] at source
    simp only [lowerArgs]
    exact (scopeFlow_lowerArg parents parent loop arg source.1).bind fun _ =>
      (scopeFlow_lowerArgs parents parent loop rest source.2).bind fun _ => ScopeFlowAction.pure parents parent loop _

theorem scopeFlow_lowerPlace (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ place : Place, ScopeTableContains parents (placeScopes parent place) →
      ScopeFlowAction parents parent loop (lowerPlace place)
  | .var localId, source => by simp only [lowerPlace]; exact ScopeFlowAction.emitDef parents parent loop _
  | .global globalId, source => by simp only [lowerPlace]; exact ScopeFlowAction.emitDef parents parent loop _
  | .field owner index, source => by
    simp only [lowerPlace]
    exact (scopeFlow_lowerPlace parents parent loop owner source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .deref expr, source => by
    simp only [lowerPlace]
    exact scopeFlow_lowerExpr parents parent loop expr source
  | .elem view index origin, source => by
    simp only [placeScopes, ScopeTableContains.append] at source
    simp only [lowerPlace]
    exact (scopeFlow_lowerView parents parent loop view source.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop index source.2).bind fun _ => ScopeFlowAction.emitDef parents parent loop _

theorem scopeFlow_lowerView (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ view : View, ScopeTableContains parents (viewScopes parent view) →
      ScopeFlowAction parents parent loop (lowerView view)
  | .of place, source => by
    simp only [lowerView]
    exact (scopeFlow_lowerPlace parents parent loop place source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _
  | .val expr, source => by
    simp only [lowerView]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.emitDef parents parent loop _

theorem scopeFlow_lowerBound (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ bound : Bound, ScopeTableContains parents (boundScopes parent bound) →
      ScopeFlowAction parents parent loop (lowerBound bound)
  | .omitted, source => ScopeFlowAction.pure parents parent loop _
  | .expr expr, source => by
    simp only [lowerBound]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.pure parents parent loop _
  | .fromEnd expr, source => by
    simp only [lowerBound]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.pure parents parent loop _

theorem scopeFlow_lowerEachSource (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ view : View, ScopeTableContains parents (viewScopes parent view) →
      ScopeFlowAction parents parent loop (lowerEachSource view)
  | .of place, source => by
    simp only [lowerEachSource]
    exact (scopeFlow_lowerPlace parents parent loop place source).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun _ => ScopeFlowAction.pure parents parent loop _
  | .val expr, source => by
    simp only [lowerEachSource]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun _ => ScopeFlowAction.pure parents parent loop _

theorem scopeFlow_lowerBlockValue (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) (want : Bool) :
    ∀ value : Option Expr, ScopeTableContains parents (match value with
        | some expr => exprScopes parent expr
        | none => []) → ScopeFlowAction parents parent loop (lowerBlockValue want value)
  | some expr, source => scopeFlow_lowerExpr parents parent loop expr source
  | none, source => by
    cases want
    · exact ScopeFlowAction.pure parents parent loop _
    · exact ScopeFlowAction.emitDef parents parent loop _

theorem scopeFlow_lowerBlock (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ block : Core.Block, ScopeTableContains parents (blockScopes parent block) →
      ScopeFlowAction parents parent loop (lowerBlock loop pre want block)
  | .mk scope stmts none, source => by
    have parts := ScopeTableContains.block source
    have parentAt : parents[scope]?.getD none = parent := by rw [parts.1]; rfl
    have inside := (ScopeFlowAction.initSlots parents (some scope) loop pre).bind fun _ =>
      (scopeFlow_lowerStmts parents (some scope) loop stmts parts.2.1).bind fun _ =>
      scopeFlow_lowerBlockValue parents (some scope) loop want none parts.2.2
    simpa only [scopedAction_eq, lowerBlock, scope_bind_assoc] using ScopeFlowAction.scoped scope inside parentAt
  | .mk scope stmts (some expr), source => by
    have parts := ScopeTableContains.block source
    have parentAt : parents[scope]?.getD none = parent := by rw [parts.1]; rfl
    have inside := (ScopeFlowAction.initSlots parents (some scope) loop pre).bind fun _ =>
      (scopeFlow_lowerStmts parents (some scope) loop stmts parts.2.1).bind fun _ =>
      scopeFlow_lowerExpr parents (some scope) loop expr parts.2.2
    simpa only [scopedAction_eq, lowerBlock, lowerBlockValue, scope_bind_assoc] using
      ScopeFlowAction.scoped scope inside parentAt

theorem scopeFlow_lowerStmts (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx)
    : ∀ stmts : List Stmt,
    ScopeTableContains parents (stmtsScopes parent stmts) → ScopeFlowAction parents parent loop (lowerStmts loop stmts)
  | [], source => ScopeFlowAction.pure parents parent loop _
  | stmt :: rest, source => by
    simp only [stmtsScopes, ScopeTableContains.append] at source
    simp only [lowerStmts]
    refine (ScopeFlowAction.isLive parents parent loop).bind fun live => ?_
    cases live
    · exact ScopeFlowAction.pure parents parent loop _
    · exact (scopeFlow_lowerStmt parents parent loop stmt source.1).bind fun _ =>
        scopeFlow_lowerStmts parents parent loop rest source.2

theorem scopeFlow_lowerPrintArgs (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx) :
    ∀ args : List PrintArg, ScopeTableContains parents (printScopes parent args) →
      ScopeFlowAction parents parent loop (lowerPrintArgs args)
  | [], source => ScopeFlowAction.pure parents parent loop _
  | .text text :: rest, source => by
    simp only [lowerPrintArgs]
    exact (scopeFlow_lowerPrintArgs parents parent loop rest source).bind fun _ => ScopeFlowAction.pure parents parent loop _
  | .expr expr :: rest, source => by
    simp only [printScopes, ScopeTableContains.append] at source
    simp only [lowerPrintArgs]
    exact (scopeFlow_lowerExpr parents parent loop expr source.1).bind fun _ =>
      (scopeFlow_lowerPrintArgs parents parent loop rest source.2).bind fun _ => ScopeFlowAction.pure parents parent loop _

theorem scopeFlow_lowerStmt (parents : Array (Option ScopeId)) (parent : Option ScopeId) (loop : Option LoopCtx)
    : ∀ stmt : Stmt, ScopeTableContains parents (stmtScopes parent stmt) →
      ScopeFlowAction parents parent loop (lowerStmt loop stmt)
  | .letS localId expr origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun value =>
      (ScopeFlowAction.coerceSlot parents parent loop localId value origin).bind fun _ =>
      ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .assign place expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop place source.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop expr source.2).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .assignOp op place expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop place source.1).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun value =>
      (scopeFlow_lowerExpr parents parent loop expr source.2).bind fun _ =>
      (ScopeFlowAction.intTyOf parents parent loop value).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .rebind localId expr origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun value =>
      (ScopeFlowAction.coerceSlot parents parent loop localId value origin).bind fun _ =>
      (ScopeFlowAction.emitDef parents parent loop _).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .expr expr origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.pure parents parent loop _
  | .append owner view origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1).bind fun _ =>
      (scopeFlow_lowerView parents parent loop view source.2).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .popN owner expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop expr source.2).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .resize owner size none origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop size source.1.2).bind fun _ =>
      (ScopeFlowAction.pure parents parent loop _).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .resize owner size (some fill) origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1.1).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop size source.1.2).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop fill source.2).bind fun value =>
      (ScopeFlowAction.pure parents parent loop (some value)).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .clear owner origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .assignWhole owner replacement origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerPlace parents parent loop owner source.1).bind fun _ =>
      (ScopeFlowAction.emitEffect parents parent loop _ rfl).bind fun _ =>
      (scopeFlow_lowerExpr parents parent loop replacement source.2).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .ifS condition yes none origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop condition source.1.1).bind fun value =>
      ScopeFlowAction.ifThen value (scopeFlow_lowerBlock parents parent loop [] false yes source.1.2)
  | .ifS condition yes (some no) origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop condition source.1.1).bind fun value =>
      ScopeFlowAction.ifArms value (scopeFlow_lowerBlock parents parent loop [] false yes source.1.2)
        (scopeFlow_lowerBlock parents parent loop [] false no source.2)
  | .while condition body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact ScopeFlowAction.whileHeader (scopeFlow_lowerExpr parents parent none condition source.1)
      (fun header depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
      (fun header depth target => scopeFlow_lowerBlock parents parent
        (some ⟨depth, target, .jump header⟩) [] false body source.2)
  | .forRange localId lower upper body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop lower source.1.1).bind fun lowerValue =>
      (scopeFlow_lowerExpr parents parent loop upper source.1.2).bind fun upperValue =>
      ScopeFlowAction.whenLive () fun _ => (ScopeFlowAction.intTyOf parents parent loop lowerValue).bind fun type =>
      ScopeFlowAction.rangeHeader type lowerValue upperValue
        (fun header counter depth target => lowerBlock
          (some ⟨depth, target, .next header type counter⟩) [(localId, counter, origin)] false body)
        (fun header counter depth target => scopeFlow_lowerBlock parents parent
          (some ⟨depth, target, .next header type counter⟩) [(localId, counter, origin)] false body source.2)
  | .forEach localId index view byRef body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scopeFlow_lowerEachSource parents parent loop view source.1).bind fun ownerView =>
      (ScopeFlowAction.regrowOf parents parent loop ownerView.1).bind fun regrow =>
      (ScopeFlowAction.eachSampled parents parent loop regrow ownerView.2).bind fun sampled =>
      (ScopeFlowAction.emitDef parents parent loop (.constInt .i64 0)).bind fun start => ScopeFlowAction.whenLive () fun _ =>
      ScopeFlowAction.eachHeader regrow ownerView.1 sampled start
        (fun header counter depth target => do
          let element ← emitDef (.refElem ownerView.2 counter)
          let elementValue ← eachElemValue localId byRef element
          lowerBlock (some ⟨depth, target, .next header .i64 counter⟩)
            ((localId, elementValue, origin) :: (match index with
              | some localIndex => [(localIndex, counter, origin)]
              | none => [])) false body)
        (fun header counter depth target =>
          (ScopeFlowAction.emitDef parents parent (some ⟨depth, target, .next header .i64 counter⟩)
            (.refElem ownerView.2 counter)).bind fun element =>
          (ScopeFlowAction.eachElemValue parents parent (some ⟨depth, target, .next header .i64 counter⟩)
            localId byRef element).bind fun elementValue =>
          scopeFlow_lowerBlock parents parent (some ⟨depth, target, .next header .i64 counter⟩)
            ((localId, elementValue, origin) :: (match index with
              | some localIndex => [(localIndex, counter, origin)]
              | none => [])) false body source.2)
  | .ret none origin, source => by
    simp only [lowerStmt]
    exact (ScopeFlowAction.pure parents parent loop _).bind fun values =>
      ScopeFlowAction.unwindReturn parents parent loop values (some origin)
  | .ret (some expr) origin, source => by
    simp only [lowerStmt]
    exact ((scopeFlow_lowerExpr parents parent loop expr source).bind fun value =>
      (ScopeFlowAction.coerceResult parents parent loop value origin).bind fun coerced =>
        ScopeFlowAction.pure parents parent loop [coerced]).bind fun values =>
      ScopeFlowAction.unwindReturn parents parent loop values (some origin)
  | .brk origin, source => by
    cases loop with
    | none => exact ScopeFlowAction.pure parents parent none _
    | some context => exact ScopeFlowAction.break parents parent context origin
  | .cont origin, source => by
    cases loop with
    | none => exact ScopeFlowAction.pure parents parent none _
    | some context => exact ScopeFlowAction.continue parents parent context origin
  | .print args origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerPrintArgs parents parent loop args source).bind fun _ => ScopeFlowAction.emitEffect parents parent loop _ rfl
  | .assertS expr origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun value => ScopeFlowAction.assertCore parents parent loop value origin
  | .abort reason origin, source => by
    simp only [lowerStmt]
    exact ScopeFlowAction.emptyTerm parents parent loop _ rfl rfl
  | .exit expr origin, source => by
    simp only [lowerStmt]
    exact (scopeFlow_lowerExpr parents parent loop expr source).bind fun _ => ScopeFlowAction.emptyTerm parents parent loop _ rfl rfl

end

end Goose.Lower.Validation
