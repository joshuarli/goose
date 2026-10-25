import Goose.Lower.Validation.ReplacementScopedOperandsTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem rhsOperands_lowerExpr (floor : Nat) : ∀ expr : Expr, RhsOperandsRun floor (lowerExpr expr)
  | .lit _ _ | .bool _ => rhsOperands_emitDef _ _ rfl
  | .structLit type expressions | .arrLit type expressions => by
    simp only [lowerExpr]
    exact rhsOperands_listDef (rhsOperands_lowerExprs floor expressions) (freshValues_lowerExprs expressions)
      _ (by intros; exact List.Subset.refl _)
  | .read place => rhsOperands_read floor place (rhsOperands_lowerPlace floor place)
  | .ref mu place => rhsOperands_ref floor mu place (rhsOperands_lowerPlace floor place)
  | .slice mu view lo hi origin => rhsOperands_slice floor mu view lo hi origin
      (rhsOperands_lowerView floor view) (rhsOperands_lowerBound floor lo) (rhsOperands_lowerBound floor hi)
  | .len view => rhsOperands_unary (rhsOperands_lowerView floor view) (advB_lowerView view)
      (freshValue_lowerView view) _ (by simp [Op.uses])
  | .un operator expr origin => rhsOperands_intUnary floor expr (rhsOperands_lowerExpr floor expr)
      _ (by simp [Op.uses])
  | .bin operator left right origin => rhsOperands_intBinary floor left right
      (rhsOperands_lowerExpr floor left) (rhsOperands_lowerExpr floor right) _ (by simp [Op.uses])
  | .cmp operator left right => rhsOperands_compare floor operator left right
      (rhsOperands_lowerExpr floor left) (rhsOperands_lowerExpr floor right)
  | .and left right | .or left right => by
    intro env before bound
    simp only [lowerExpr]
    apply RhsOperandsAt.bindFresh bound (rhsOperands_lowerExpr floor left env before bound)
      (advB_lowerExpr left) (freshValue_lowerExpr left)
    intro value middle _ middleBound valueFresh
    exact rhsOperands_shortCircuit floor _ value (advB_lowerExpr right) (freshValue_lowerExpr right)
      (rhsOperands_lowerExpr floor right) env middle middleBound valueFresh
  | .not expr => rhsOperands_unary (rhsOperands_lowerExpr floor expr) (advB_lowerExpr expr)
      (freshValue_lowerExpr expr) _ (by simp [Op.uses])
  | .conv kind target expr origin => rhsOperands_intUnary floor expr (rhsOperands_lowerExpr floor expr)
      _ (by simp [Op.uses])
  | .call context args origin => rhsOperands_call floor context args origin (rhsOperands_lowerArgs floor args)
  | .push place expr origin => rhsOperands_binary (rhsOperands_lowerPlace floor place)
      (rhsOperands_lowerExpr floor expr) (advB_lowerPlace place) (advB_lowerExpr expr)
      (freshValue_lowerPlace place) (freshValue_lowerExpr expr) (dead_lowerExpr expr) _ (by simp [Op.uses])
  | .pop place origin => rhsOperands_unary (rhsOperands_lowerPlace floor place) (advB_lowerPlace place)
      (freshValue_lowerPlace place) _ (by simp [Op.uses])
  | .ifE condition yes no => rhsOperands_ifExpression floor condition yes no
      (rhsOperands_lowerExpr floor condition) (rhsOperands_lowerBlock floor yes) (rhsOperands_lowerBlock floor no)
  | .blockE block => fun env state bound =>
      rhsOperands_lowerBlock floor block none [] true env state bound trivial (by simp [RhsPreFresh])
  | .fill type expr => rhsOperands_unary (rhsOperands_lowerExpr floor expr) (advB_lowerExpr expr)
      (freshValue_lowerExpr expr) _ (by simp [Op.uses])

theorem rhsOperands_lowerPlace (floor : Nat) : ∀ place : Place, RhsOperandsRun floor (lowerPlace place)
  | .var _ | .global _ => rhsOperands_emitDef _ _ rfl
  | .deref expr => rhsOperands_lowerExpr floor expr
  | .field place field => rhsOperands_unary (rhsOperands_lowerPlace floor place) (advB_lowerPlace place)
      (freshValue_lowerPlace place) _ (by simp [Op.uses])
  | .elem view index origin => rhsOperands_binary (rhsOperands_lowerView floor view)
      (rhsOperands_lowerExpr floor index) (advB_lowerView view) (advB_lowerExpr index)
      (freshValue_lowerView view) (freshValue_lowerExpr index) (dead_lowerExpr index) _ (by simp [Op.uses])

theorem rhsOperands_lowerView (floor : Nat) : ∀ view : View, RhsOperandsRun floor (lowerView view)
  | .of place => rhsOperands_unary (rhsOperands_lowerPlace floor place) (advB_lowerPlace place)
      (freshValue_lowerPlace place) _ (by simp [Op.uses])
  | .val expr => rhsOperands_unary (rhsOperands_lowerExpr floor expr) (advB_lowerExpr expr)
      (freshValue_lowerExpr expr) _ (by simp [Op.uses])

theorem rhsOperands_lowerBound (floor : Nat) : ∀ bound : Bound, RhsOperandsRun floor (lowerBound bound)
  | .omitted => fun env before _ => RhsOperandsAt.pure _ _ _ _
  | .expr expr => rhsOperands_bound expr (rhsOperands_lowerExpr floor expr) false
  | .fromEnd expr => rhsOperands_bound expr (rhsOperands_lowerExpr floor expr) true

theorem rhsOperands_lowerArg (floor : Nat) : ∀ arg : Arg, RhsOperandsRun floor (lowerArg arg)
  | .byVal expr => rhsOperands_lowerExpr floor expr
  | .byRef mu place => rhsOperands_borrowArg floor mu place (rhsOperands_lowerPlace floor place)

theorem rhsOperands_lowerExprs (floor : Nat) : ∀ expressions : List Expr,
    RhsOperandsRun floor (lowerExprs expressions)
  | [] => fun env before _ => RhsOperandsAt.pure _ _ _ _
  | expr :: rest => rhsOperands_valueListCons (rhsOperands_lowerExpr floor expr)
      (rhsOperands_lowerExprs floor rest) (advB_lowerExpr expr)

theorem rhsOperands_lowerArgs (floor : Nat) : ∀ args : List Arg, RhsOperandsRun floor (lowerArgs args)
  | [] => fun env before _ => RhsOperandsAt.pure _ _ _ _
  | arg :: rest => rhsOperands_valueListCons (rhsOperands_lowerArg floor arg)
      (rhsOperands_lowerArgs floor rest) (advB_lowerArg arg)

theorem rhsOperands_lowerBlockValue (floor : Nat) (want : Bool) : ∀ value : Option Expr,
    RhsOperandsRun floor (lowerBlockValue want value)
  | some expr => rhsOperands_lowerExpr floor expr
  | none => by
    cases want
    · exact fun env before _ => RhsOperandsAt.pure _ _ _ _
    · exact rhsOperands_emitDef _ _ rfl

theorem rhsOperands_lowerBlock (floor : Nat) : ∀ block : Core.Block, RhsBlockChild floor block
  | .mk scope statements value => by
    intro loop pre want env before bound loopFresh preFresh
    exact rhsOperands_block_live floor loop pre want scope statements value
      (rhsOperands_lowerStmts floor statements loop loopFresh)
      (rhsOperands_lowerBlockValue floor want value) env before bound preFresh

theorem rhsOperands_lowerStmts (floor : Nat) : ∀ statements : List Stmt, ∀ loop,
    RhsLoopFresh floor loop → RhsOperandsRun floor (lowerStmts loop statements)
  | [], loop, _ => fun env before _ => RhsOperandsAt.pure _ _ _ _
  | statement :: rest, loop, fresh => rhsOperands_statementsCons floor loop statement rest
      (rhsOperands_lowerStmt floor statement loop fresh) (rhsOperands_lowerStmts floor rest loop fresh)

theorem rhsOperands_lowerPrintArgs (floor : Nat) : ∀ args : List PrintArg,
    RhsOperandsRun floor (lowerPrintArgs args)
  | [] => fun env before _ => RhsOperandsAt.pure _ _ _ _
  | .text text :: rest => by
    intro env before bound
    simp only [lowerPrintArgs]
    exact (rhsOperands_lowerPrintArgs floor rest env before bound).bind (RhsOperandsAt.pure _ _ _ _)
  | .expr expr :: rest => by
    intro env before bound
    simp only [lowerPrintArgs]
    apply RhsOperandsAt.bindRun (rhsOperands_lowerExpr floor expr env before bound)
    intro value middle run
    exact (rhsOperands_lowerPrintArgs floor rest env middle
      (Nat.le_trans bound (advB_lowerExpr expr env before value middle run).vals)).bind
      (RhsOperandsAt.pure _ _ _ _)

theorem rhsOperands_lowerStmt (floor : Nat) : ∀ statement : Stmt, ∀ loop,
    RhsLoopFresh floor loop → RhsOperandsRun floor (lowerStmt loop statement)
  | .letS slot expr origin, loop, _ => by
    simp only [lowerStmt]
    exact rhsOperands_unaryEffect (rhsOperands_coerceSlot floor slot expr origin (rhsOperands_lowerExpr floor expr))
      (AdvB.bind (advB_lowerExpr expr) fun value => advB_coerceSlot slot value origin)
      (freshValue_coerceSlot slot expr origin) (fun value => .slotInit slot value (some origin))
      (by simp [Effect.uses])
  | .assign place expr origin, loop, _ => rhsOperands_binaryEffect
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerExpr floor expr)
      (advB_lowerPlace place) (advB_lowerExpr expr) (freshValue_lowerPlace place)
      (freshValue_lowerExpr expr) (dead_lowerExpr expr) _ (by simp [Effect.uses])
  | .assignOp operator place expr origin, loop, _ => rhsOperands_assignOp floor loop operator place expr origin
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerExpr floor expr)
  | .rebind slot expr origin, loop, _ => by
    simp only [lowerStmt]
    exact rhsOperands_binaryEffect (rhsOperands_coerceSlot floor slot expr origin (rhsOperands_lowerExpr floor expr))
      (rhsOperands_emitDef floor (.slotAddr slot) rfl)
      (AdvB.bind (advB_lowerExpr expr) fun value => advB_coerceSlot slot value origin) (advB_emitDef _)
      (freshValue_coerceSlot slot expr origin) (freshValue_emitDef _) (dead_emitDef _)
      (fun value address => .store address value (some origin)) (by simp [Effect.uses, List.subset_def])
  | .expr expr origin, loop, _ => by
    intro env before bound
    exact (rhsOperands_lowerExpr floor expr env before bound).bind (RhsOperandsAt.pure _ _ _ _)
  | .append place view origin, loop, _ => rhsOperands_binaryEffect
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerView floor view)
      (advB_lowerPlace place) (advB_lowerView view) (freshValue_lowerPlace place)
      (freshValue_lowerView view) (dead_lowerView view) _ (by simp [Effect.uses])
  | .popN place expr origin, loop, _ => rhsOperands_binaryEffect
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerExpr floor expr)
      (advB_lowerPlace place) (advB_lowerExpr expr) (freshValue_lowerPlace place)
      (freshValue_lowerExpr expr) (dead_lowerExpr expr) _ (by simp [Effect.uses])
  | .resize place size fill origin, loop, _ => rhsOperands_resize floor loop place size fill origin
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerExpr floor size)
      (fun expr equal => by cases equal; exact rhsOperands_lowerExpr floor expr)
  | .clear place origin, loop, _ => rhsOperands_unaryEffect (rhsOperands_lowerPlace floor place)
      (advB_lowerPlace place) (freshValue_lowerPlace place) _ (by simp [Effect.uses])
  | .assignWhole place expr origin, loop, _ => rhsOperands_assignWhole floor loop place expr origin
      (rhsOperands_lowerPlace floor place) (rhsOperands_lowerExpr floor expr)
  | .ifS condition yes no origin, loop, fresh => rhsOperands_ifStatement floor loop condition yes no origin fresh
      (rhsOperands_lowerExpr floor condition) (rhsOperands_lowerBlock floor yes)
      (fun block equal => by cases equal; exact rhsOperands_lowerBlock floor block)
  | .while condition body origin, loop, _ => rhsOperands_whileStatement floor loop condition body origin
      (rhsOperands_lowerExpr floor condition) (rhsOperands_lowerBlock floor body)
  | .forRange slot lo hi body origin, loop, _ => rhsOperands_rangeStatement floor loop slot lo hi body origin
      (rhsOperands_lowerExpr floor lo) (rhsOperands_lowerExpr floor hi) (rhsOperands_lowerBlock floor body)
  | .forEach slot index view byRef body origin, loop, _ => by
    apply rhsOperands_eachStatement floor loop slot index view byRef body origin
    · cases view with
      | of place =>
        apply rhsOperands_eachSource floor (.of place)
        · intro actual equal
          cases equal
          exact rhsOperands_lowerPlace floor place
        · intro expression equal
          cases equal
      | val expr =>
        apply rhsOperands_eachSource floor (.val expr)
        · intro place equal
          cases equal
        · intro actual equal
          cases equal
          exact rhsOperands_lowerExpr floor expr
    · exact rhsOperands_lowerBlock floor body
  | .ret value origin, loop, _ => rhsOperands_return floor loop value origin
      (fun expr equal => by cases equal; exact rhsOperands_lowerExpr floor expr)
  | .brk origin, loop, _ => by
    intro env before bound
    simp only [lowerStmt]
    cases loop
    · exact RhsOperandsAt.pure _ _ _ _
    · exact (RhsOperandsAt.leaveTo _ _ _ _).bind
        (RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses]))
  | .cont origin, loop, fresh => rhsOperands_continue floor loop origin fresh
  | .print args origin, loop, _ => rhsOperands_print floor loop args origin (rhsOperands_lowerPrintArgs floor args)
  | .assertS condition origin, loop, _ => rhsOperands_assertStatement floor loop condition origin
      (rhsOperands_lowerExpr floor condition)
  | .abort message origin, loop, _ => fun env before _ =>
      RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses])
  | .exit expr origin, loop, _ => rhsOperands_exit floor loop expr origin (rhsOperands_lowerExpr floor expr)

end

end Goose.Lower.Validation
