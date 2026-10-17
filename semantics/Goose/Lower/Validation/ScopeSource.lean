import Goose.Lower.Validation.ScopeControl
import Goose.Lower.Validation.ScopeBlocks
import Goose.Lower.Validation.ScopeUnwindActions
import Goose.Lower.Validation.ScopeLexical

set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem scope_lowerExpr (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ expr : Expr, ScopeTableContains parents (exprScopes parent expr) →
      ScopeAction parents parent (lowerExpr expr)
  | .structLit type exprs, source => by
    simp only [lowerExpr]
    exact (scope_lowerExprs parents parent exprs source).bind fun _ => ScopeAction.emitDef parents parent _
  | .lit type value, source => by
    simp only [lowerExpr]
    exact ScopeAction.emitDef parents parent _
  | .bool value, source => by
    simp only [lowerExpr]
    exact ScopeAction.emitDef parents parent _
  | .read place, source => by
    simp only [lowerExpr]
    exact (scope_lowerPlace parents parent place source).bind fun _ => ScopeAction.emitDef parents parent _
  | .ref mutability place, source => by
    simp only [lowerExpr]
    exact (scope_lowerPlace parents parent place source).bind fun value => ScopeAction.borrowTo parents parent mutability value
  | .slice mutability view lower upper origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerView parents parent view source.1.1).bind fun _ =>
      (scope_lowerBound parents parent lower source.1.2).bind fun _ =>
      (scope_lowerBound parents parent upper source.2).bind fun _ => ScopeAction.emitDef parents parent _
  | .len view, source => by
    simp only [lowerExpr]
    exact (scope_lowerView parents parent view source).bind fun _ => ScopeAction.emitDef parents parent _
  | .un op expr origin, source => by
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent expr source).bind fun value =>
      (ScopeAction.intTyOf parents parent value).bind fun _ => ScopeAction.emitDef parents parent _
  | .bin op left right origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent left source.1).bind fun value =>
      (scope_lowerExpr parents parent right source.2).bind fun _ =>
      (ScopeAction.intTyOf parents parent value).bind fun _ => ScopeAction.emitDef parents parent _
  | .cmp op left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    refine (scope_lowerExpr parents parent left source.1).bind fun value =>
      (scope_lowerExpr parents parent right source.2).bind fun _ =>
      (ScopeAction.valTy parents parent value).bind fun type => ?_
    cases type with
    | data type => cases type <;> exact ScopeAction.emitDef parents parent _
    | view _ _ => exact ScopeAction.emitDef parents parent _
  | .and left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent left source.1).bind fun value =>
      ScopeAction.shortCircuit true value (scope_lowerExpr parents parent right source.2)
  | .or left right, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent left source.1).bind fun value =>
      ScopeAction.shortCircuit false value (scope_lowerExpr parents parent right source.2)
  | .not expr, source => by
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.emitDef parents parent _
  | .conv kind target expr origin, source => by
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent expr source).bind fun value =>
      (ScopeAction.intTyOf parents parent value).bind fun _ => ScopeAction.emitDef parents parent _
  | .call context args origin, source => by
    simp only [lowerExpr]
    refine (scope_lowerArgs parents parent args source).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun result =>
      (ScopeAction.read parents parent).bind fun env => ?_
    cases noReturn : env.mod.noReturn context <;> simp only [Bool.false_eq_true, reduceIte]
    · exact ScopeAction.pure parents parent _
    · exact (ScopeAction.emitNeutralTerm parents parent .unreachable rfl).bind fun _ => ScopeAction.pure parents parent result
  | .push owner expr origin, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerPlace parents parent owner source.1).bind fun _ =>
      (scope_lowerExpr parents parent expr source.2).bind fun _ => ScopeAction.emitDef parents parent _
  | .pop owner origin, source => by
    simp only [lowerExpr]
    exact (scope_lowerPlace parents parent owner source).bind fun _ => ScopeAction.emitDef parents parent _
  | .ifE condition yes no, source => by
    simp only [exprScopes, ScopeTableContains.append] at source
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent condition source.1.1).bind fun value =>
      ScopeAction.ifValue value (sourceBlockScope yes)
        (scope_lowerBlock parents parent none [] true yes source.1.2)
        (scope_lowerBlock parents parent none [] true no source.2)
  | .blockE block, source => by
    simp only [lowerExpr]
    exact scope_lowerBlock parents parent none [] true block source
  | .arrLit type exprs, source => by
    simp only [lowerExpr]
    exact (scope_lowerExprs parents parent exprs source).bind fun _ => ScopeAction.emitDef parents parent _
  | .fill type expr, source => by
    simp only [lowerExpr]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.emitDef parents parent _

theorem scope_lowerExprs (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ exprs : List Expr, ScopeTableContains parents (exprsScopes parent exprs) →
      ScopeAction parents parent (lowerExprs exprs)
  | [], source => ScopeAction.pure parents parent _
  | expr :: rest, source => by
    simp only [exprsScopes, ScopeTableContains.append] at source
    simp only [lowerExprs]
    exact (scope_lowerExpr parents parent expr source.1).bind fun _ =>
      (scope_lowerExprs parents parent rest source.2).bind fun _ => ScopeAction.pure parents parent _

theorem scope_lowerArg (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ arg : Arg, ScopeTableContains parents (argsScopes parent [arg]) →
      ScopeAction parents parent (lowerArg arg)
  | .byVal expr, source => by
    simp only [argsScopes, List.append_nil] at source
    exact scope_lowerExpr parents parent expr source
  | .byRef mutability place, source => by
    simp only [argsScopes, List.append_nil] at source
    simp only [lowerArg]
    exact (scope_lowerPlace parents parent place source).bind fun value =>
      ScopeAction.borrowTo parents parent mutability value

theorem scope_lowerArgs (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ args : List Arg, ScopeTableContains parents (argsScopes parent args) →
      ScopeAction parents parent (lowerArgs args)
  | [], source => ScopeAction.pure parents parent _
  | arg :: rest, source => by
    have split : argsScopes parent (arg :: rest) = argsScopes parent [arg] ++ argsScopes parent rest := by
      cases arg <;> simp [argsScopes]
    rw [split, ScopeTableContains.append] at source
    simp only [lowerArgs]
    exact (scope_lowerArg parents parent arg source.1).bind fun _ =>
      (scope_lowerArgs parents parent rest source.2).bind fun _ => ScopeAction.pure parents parent _

theorem scope_lowerPlace (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ place : Place, ScopeTableContains parents (placeScopes parent place) →
      ScopeAction parents parent (lowerPlace place)
  | .var localId, source => by simp only [lowerPlace]; exact ScopeAction.emitDef parents parent _
  | .global globalId, source => by simp only [lowerPlace]; exact ScopeAction.emitDef parents parent _
  | .field owner index, source => by
    simp only [lowerPlace]
    exact (scope_lowerPlace parents parent owner source).bind fun _ => ScopeAction.emitDef parents parent _
  | .deref expr, source => by
    simp only [lowerPlace]
    exact scope_lowerExpr parents parent expr source
  | .elem view index origin, source => by
    simp only [placeScopes, ScopeTableContains.append] at source
    simp only [lowerPlace]
    exact (scope_lowerView parents parent view source.1).bind fun _ =>
      (scope_lowerExpr parents parent index source.2).bind fun _ => ScopeAction.emitDef parents parent _

theorem scope_lowerView (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ view : View, ScopeTableContains parents (viewScopes parent view) →
      ScopeAction parents parent (lowerView view)
  | .of place, source => by
    simp only [lowerView]
    exact (scope_lowerPlace parents parent place source).bind fun _ => ScopeAction.emitDef parents parent _
  | .val expr, source => by
    simp only [lowerView]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.emitDef parents parent _

theorem scope_lowerBound (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ bound : Bound, ScopeTableContains parents (boundScopes parent bound) →
      ScopeAction parents parent (lowerBound bound)
  | .omitted, source => ScopeAction.pure parents parent _
  | .expr expr, source => by
    simp only [lowerBound]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.pure parents parent _
  | .fromEnd expr, source => by
    simp only [lowerBound]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.pure parents parent _

theorem scope_lowerEachSource (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ view : View, ScopeTableContains parents (viewScopes parent view) →
      ScopeAction parents parent (lowerEachSource view)
  | .of place, source => by
    simp only [lowerEachSource]
    exact (scope_lowerPlace parents parent place source).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun _ => ScopeAction.pure parents parent _
  | .val expr, source => by
    simp only [lowerEachSource]
    exact (scope_lowerExpr parents parent expr source).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun _ => ScopeAction.pure parents parent _

theorem scope_lowerBlockValue (parents : Array (Option ScopeId)) (parent : Option ScopeId) (want : Bool) :
    ∀ value : Option Expr, ScopeTableContains parents (match value with
        | some expr => exprScopes parent expr
        | none => []) → ScopeAction parents parent (lowerBlockValue want value)
  | some expr, source => scope_lowerExpr parents parent expr source
  | none, source => by
    cases want
    · exact ScopeAction.pure parents parent _
    · exact ScopeAction.emitDef parents parent _

theorem scope_lowerBlock (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ block : Core.Block, ScopeTableContains parents (blockScopes parent block) →
      ScopeAction parents parent (lowerBlock loop pre want block)
  | .mk scope stmts none, source => by
    have parts := ScopeTableContains.block source
    have parentAt : parents[scope]?.getD none = parent := by rw [parts.1]; rfl
    have inside := (ScopeAction.initSlots parents (some scope) pre).bind fun _ =>
      (scope_lowerStmts parents (some scope) loop stmts parts.2.1).bind fun _ =>
      scope_lowerBlockValue parents (some scope) want none parts.2.2
    simpa only [scopedAction_eq, lowerBlock, scope_bind_assoc] using ScopeAction.scoped scope inside parentAt
  | .mk scope stmts (some expr), source => by
    have parts := ScopeTableContains.block source
    have parentAt : parents[scope]?.getD none = parent := by rw [parts.1]; rfl
    have inside := (ScopeAction.initSlots parents (some scope) pre).bind fun _ =>
      (scope_lowerStmts parents (some scope) loop stmts parts.2.1).bind fun _ =>
      scope_lowerExpr parents (some scope) expr parts.2.2
    simpa only [scopedAction_eq, lowerBlock, lowerBlockValue, scope_bind_assoc] using
      ScopeAction.scoped scope inside parentAt

theorem scope_lowerStmts (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ∀ stmts : List Stmt,
    ScopeTableContains parents (stmtsScopes parent stmts) → ScopeAction parents parent (lowerStmts loop stmts)
  | [], source => ScopeAction.pure parents parent _
  | stmt :: rest, source => by
    simp only [stmtsScopes, ScopeTableContains.append] at source
    simp only [lowerStmts]
    refine (ScopeAction.isLive parents parent).bind fun live => ?_
    cases live
    · exact ScopeAction.pure parents parent _
    · exact (scope_lowerStmt parents parent loop stmt source.1).bind fun _ =>
        scope_lowerStmts parents parent loop rest source.2

theorem scope_lowerPrintArgs (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ args : List PrintArg, ScopeTableContains parents (printScopes parent args) →
      ScopeAction parents parent (lowerPrintArgs args)
  | [], source => ScopeAction.pure parents parent _
  | .text text :: rest, source => by
    simp only [lowerPrintArgs]
    exact (scope_lowerPrintArgs parents parent rest source).bind fun _ => ScopeAction.pure parents parent _
  | .expr expr :: rest, source => by
    simp only [printScopes, ScopeTableContains.append] at source
    simp only [lowerPrintArgs]
    exact (scope_lowerExpr parents parent expr source.1).bind fun _ =>
      (scope_lowerPrintArgs parents parent rest source.2).bind fun _ => ScopeAction.pure parents parent _

theorem scope_lowerStmt (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) : ∀ stmt : Stmt, ScopeTableContains parents (stmtScopes parent stmt) →
      ScopeAction parents parent (lowerStmt loop stmt)
  | .letS localId expr origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent expr source).bind fun value =>
      (ScopeAction.coerceSlot parents parent localId value origin).bind fun _ =>
      ScopeAction.emitNeutralEffect parents parent _ rfl
  | .assign place expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent place source.1).bind fun _ =>
      (scope_lowerExpr parents parent expr source.2).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .assignOp op place expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent place source.1).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun value =>
      (scope_lowerExpr parents parent expr source.2).bind fun _ =>
      (ScopeAction.intTyOf parents parent value).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .rebind localId expr origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent expr source).bind fun value =>
      (ScopeAction.coerceSlot parents parent localId value origin).bind fun _ =>
      (ScopeAction.emitDef parents parent _).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .expr expr origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.pure parents parent _
  | .append owner view origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source.1).bind fun _ =>
      (scope_lowerView parents parent view source.2).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .popN owner expr origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source.1).bind fun _ =>
      (scope_lowerExpr parents parent expr source.2).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .resize owner size none origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source.1.1).bind fun _ =>
      (scope_lowerExpr parents parent size source.1.2).bind fun _ =>
      (ScopeAction.pure parents parent _).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .resize owner size (some fill) origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source.1.1).bind fun _ =>
      (scope_lowerExpr parents parent size source.1.2).bind fun _ =>
      (scope_lowerExpr parents parent fill source.2).bind fun value =>
      (ScopeAction.pure parents parent (some value)).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .clear owner origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .assignWhole owner replacement origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerPlace parents parent owner source.1).bind fun _ =>
      (ScopeAction.emitNeutralEffect parents parent _ rfl).bind fun _ =>
      (scope_lowerExpr parents parent replacement source.2).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .ifS condition yes none origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent condition source.1.1).bind fun value =>
      ScopeAction.ifThen value (scope_lowerBlock parents parent loop [] false yes source.1.2)
  | .ifS condition yes (some no) origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent condition source.1.1).bind fun value =>
      ScopeAction.ifArms value (scope_lowerBlock parents parent loop [] false yes source.1.2)
        (scope_lowerBlock parents parent loop [] false no source.2)
  | .while condition body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact ScopeAction.header [] [] advB_newBlock0 fun header _ =>
      ScopeAction.lowerWhile header (scope_lowerExpr parents parent condition source.1)
        (fun depth target => scope_lowerBlock parents parent (some ⟨depth, target, .jump header⟩) [] false body source.2)
  | .forRange localId lower upper body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent lower source.1.1).bind fun lowerValue =>
      (scope_lowerExpr parents parent upper source.1.2).bind fun upperValue =>
      ScopeAction.whenLive () fun _ => (ScopeAction.intTyOf parents parent lowerValue).bind fun type =>
      ScopeAction.header [.data (.int type)] [lowerValue] (advB_newBlock1 _) fun header params =>
        ScopeAction.lowerRange type (params.headD 0) upperValue header
          (fun depth target => scope_lowerBlock parents parent
            (some ⟨depth, target, .next header type (params.headD 0)⟩)
            [(localId, params.headD 0, origin)] false body source.2)
  | .forEach localId index view byRef body origin, source => by
    simp only [stmtScopes, ScopeTableContains.append] at source
    simp only [lowerStmt]
    exact (scope_lowerEachSource parents parent view source.1).bind fun ownerView =>
      (ScopeAction.regrowOf parents parent ownerView.1).bind fun regrow =>
      (ScopeAction.eachSampled parents parent regrow ownerView.2).bind fun sampled =>
      (ScopeAction.emitDef parents parent (.constInt .i64 0)).bind fun start => ScopeAction.whenLive () fun _ =>
      ScopeAction.header [.data (.int .i64)] [start] (advB_newBlock1 _) fun header params =>
        ScopeAction.lowerEach regrow ownerView.1 sampled header (params.headD 0)
          (fun depth target => (ScopeAction.emitDef parents parent (.refElem ownerView.2 (params.headD 0))).bind fun element =>
            (ScopeAction.eachElemValue parents parent localId byRef element).bind fun elementValue =>
              scope_lowerBlock parents parent (some ⟨depth, target, .next header .i64 (params.headD 0)⟩)
                ((localId, elementValue, origin) :: (match index with
                  | some localIndex => [(localIndex, params.headD 0, origin)]
                  | none => [])) false body source.2)
  | .ret none origin, source => by
    simp only [lowerStmt]
    exact (ScopeAction.pure parents parent _).bind fun values =>
      ScopeAction.unwindReturn parents parent values (some origin)
  | .ret (some expr) origin, source => by
    simp only [lowerStmt]
    exact ((scope_lowerExpr parents parent expr source).bind fun value =>
      (ScopeAction.coerceResult parents parent value origin).bind fun coerced =>
        ScopeAction.pure parents parent [coerced]).bind fun values =>
      ScopeAction.unwindReturn parents parent values (some origin)
  | .brk origin, source => by
    cases loop with
    | none => exact ScopeAction.pure parents parent _
    | some loop => exact ScopeAction.unwindBranch parents parent loop.depth loop.breakTo []
  | .cont origin, source => by
    cases loop with
    | none => exact ScopeAction.pure parents parent _
    | some loop =>
      cases continued : loop.cont with
      | jump header =>
        simpa only [lowerStmt, continued] using ScopeAction.unwindBranch parents parent loop.depth header []
      | next header type counter =>
        simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using ScopeAction.unwindNext parents parent loop.depth type counter header
  | .print args origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerPrintArgs parents parent args source).bind fun _ => ScopeAction.emitNeutralEffect parents parent _ rfl
  | .assertS expr origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent expr source).bind fun value => ScopeAction.assertCore parents parent value origin
  | .abort reason origin, source => by
    simp only [lowerStmt]
    exact ScopeAction.emitNeutralTerm parents parent _ rfl
  | .exit expr origin, source => by
    simp only [lowerStmt]
    exact (scope_lowerExpr parents parent expr source).bind fun _ => ScopeAction.emitNeutralTerm parents parent _ rfl

end

end Goose.Lower.Validation
