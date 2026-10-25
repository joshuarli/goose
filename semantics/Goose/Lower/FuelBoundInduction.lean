import Goose.Lower.FuelBoundBudget
import Goose.Lower.FuelBoundSizeFacts
import Goose.Lower.FuelBoundTypedMethods
import Goose.Lower.FuelBoundCallExpressions
import Goose.Lower.FuelBoundModule
import Goose.Lower.FuelBoundExpressionsScalar
import Goose.Lower.FuelBoundExpressionsAccess
import Goose.Lower.FuelBoundExpressionsAggregates
import Goose.Lower.FuelBoundExpressionsMemory
import Goose.Lower.FuelBoundExpressionsElements
import Goose.Lower.FuelBoundExpressionsDereference
import Goose.Lower.FuelBoundControlShortCircuit
import Goose.Lower.FuelBoundControlBranches
import Goose.Lower.FuelBoundControlBranchesStatements
import Goose.Lower.FuelBoundBlocks
import Goose.Lower.FuelBoundBlocksConstructor
import Goose.Lower.FuelBoundControlWhile
import Goose.Lower.FuelBoundControlRange
import Goose.Lower.FuelBoundControlRangeStatement
import Goose.Lower.FuelBoundControlEach
import Goose.Lower.FuelBoundControlEachStatement
import Goose.Lower.FuelBoundOutput
import Goose.Lower.FuelBoundMutationsWrites
import Goose.Lower.FuelBoundMutationsPopN
import Goose.Lower.FuelBoundMutationsResize
import Goose.Lower.FuelBoundBindings

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private structure FuelBoundFamily (cap fuel size : Nat) (cfg : Cfg) : Prop where
  expr : ∀ (results : List Ty) (expression : Expr), SourceFuelSize.expr expression ≤ size →
    TypedExprFuelBound (reflectionFuelBound cap fuel size) fuel cfg results expression
  place : ∀ (results : List Ty) (place : Place), SourceFuelSize.place place ≤ size →
    TypedPlaceFuelBound (reflectionFuelBound cap fuel size) fuel cfg results place
  view : ∀ (results : List Ty) (view : View), SourceFuelSize.view view ≤ size →
    TypedViewFuelBound (reflectionFuelBound cap fuel size) fuel cfg results view
  boundary : ∀ (results : List Ty) (boundary : Bound), SourceFuelSize.boundary boundary ≤ size →
    TypedBoundFuelBound (reflectionFuelBound cap fuel size) fuel cfg results boundary
  arg : ∀ (results : List Ty) (argument : Arg), SourceFuelSize.arg argument ≤ size →
    TypedArgFuelBound (reflectionFuelBound cap fuel size) fuel cfg results argument
  block : ∀ (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) (want : Bool) (body : Core.Block), SourceFuelSize.block body ≤ size →
    TypedBlockFuelBound (reflectionFuelBound cap fuel size) fuel cfg results loop pre pre' want body
  statements : ∀ (results : List Ty) (loop : Option LoopCtx) (statements : List Stmt), SourceFuelSize.stmts statements ≤ size →
    TypedStatementsFuelBound (reflectionFuelBound cap fuel size) fuel cfg results loop statements
  statement : ∀ (results : List Ty) (loop : Option LoopCtx) (statement : Stmt), SourceFuelSize.stmt statement ≤ size →
    TypedStatementFuelBound (reflectionFuelBound cap fuel size) fuel cfg results loop statement
  whileLoop : ∀ (results : List Ty) (condition : Expr) (body : Core.Block) (origin : OriginId), SourceFuelSize.expr condition + SourceFuelSize.block body ≤ size →
    TypedWhileFuelBound (reflectionFuelBound cap fuel size) fuel cfg results condition body origin
  rangeLoop : ∀ (results : List Ty) (index : VarId) (low high : Expr) (body : Core.Block) (origin : OriginId), SourceFuelSize.block body ≤ size →
    TypedRangeFuelBound (reflectionFuelBound cap fuel size) fuel cfg results index low high body origin
  eachLoop : ∀ (results : List Ty) (variableId : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId), SourceFuelSize.block body ≤ size →
    TypedEachFuelBound (reflectionFuelBound cap fuel size) fuel cfg results variableId index view byRef body origin

private theorem fuelBoundRank {fuel residual size child : Nat}
    (earlier : residual ≤ fuel) (smaller : child < size) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (residual,child) (fuel,size) := by
  rcases Nat.lt_or_eq_of_le earlier with less | rfl
  · exact Prod.Lex.left _ _ less
  · exact Prod.Lex.right _ smaller

private theorem fuelBoundFamily (cap : Nat) (cfg : Cfg)
    (moduleBound : moduleSyntaxCap cfg.mod ≤ cap) (fuel size : Nat) (syntaxBound : size ≤ cap) :
    FuelBoundFamily cap fuel size cfg := by
  let budget := reflectionFuelBound cap fuel size - 8
  have spend (cost : Nat) (small : cost ≤ 8) : budget + cost ≤ reflectionFuelBound cap fuel size :=
    reflectionFuelBound_spare_cost small
  have leaf : 1 ≤ reflectionFuelBound cap fuel size :=
    Nat.le_trans (by decide : 1 ≤ 8) (reflectionFuelBound_minimum cap fuel size)
  have childExpr (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (expression : Expr)
      (smaller : SourceFuelSize.expr expression < size) : TypedExprFuelBound budget residual cfg results expression :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.expr expression) (by omega)).expr
      results expression (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childPlace (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (place : Place)
      (smaller : SourceFuelSize.place place < size) : TypedPlaceFuelBound budget residual cfg results place :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.place place) (by omega)).place
      results place (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childView (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (view : View)
      (smaller : SourceFuelSize.view view < size) : TypedViewFuelBound budget residual cfg results view :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.view view) (by omega)).view
      results view (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childBoundary (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (boundary : Bound)
      (smaller : SourceFuelSize.boundary boundary < size) : TypedBoundFuelBound budget residual cfg results boundary :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.boundary boundary) (by omega)).boundary
      results boundary (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childArg (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (argument : Arg)
      (smaller : SourceFuelSize.arg argument < size) : TypedArgFuelBound budget residual cfg results argument :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.arg argument) (by omega)).arg
      results argument (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childBlock (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) (want : Bool) (body : Core.Block)
      (smaller : SourceFuelSize.block body < size) : TypedBlockFuelBound budget residual cfg results loop pre pre' want body :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.block body) (by omega)).block
      results loop pre pre' want body (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childStatements (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (loop : Option LoopCtx) (statements : List Stmt)
      (smaller : SourceFuelSize.stmts statements < size) : TypedStatementsFuelBound budget residual cfg results loop statements :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.stmts statements) (by omega)).statements
      results loop statements (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have childStatement (residual : Nat) (earlier : residual ≤ fuel) (results : List Ty) (loop : Option LoopCtx) (statement : Stmt)
      (smaller : SourceFuelSize.stmt statement < size) : TypedStatementFuelBound budget residual cfg results loop statement :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.stmt statement) (by omega)).statement
      results loop statement (Nat.le_refl _)).source_mono (reflectionFuelBound_child_spare earlier smaller)
  have earlierBlock (residual : Nat) (earlier : residual < fuel) (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) (want : Bool) (body : Core.Block)
      (bounded : SourceFuelSize.block body ≤ cap) : TypedBlockFuelBound budget residual cfg results loop pre pre' want body :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.block body) bounded).block
      results loop pre pre' want body (Nat.le_refl _)).source_mono (reflectionFuelBound_recursive_spare earlier bounded)
  have earlierWhileLoop (residual : Nat) (earlier : residual < fuel) (results : List Ty) (condition : Expr) (body : Core.Block) (origin : OriginId)
      (bounded : SourceFuelSize.expr condition + SourceFuelSize.block body ≤ cap) : TypedWhileFuelBound budget residual cfg results condition body origin :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.expr condition + SourceFuelSize.block body) bounded).whileLoop
      results condition body origin (Nat.le_refl _)).source_mono (reflectionFuelBound_recursive_spare earlier bounded)
  have earlierRangeLoop (residual : Nat) (earlier : residual < fuel) (results : List Ty) (index : VarId) (low high : Expr) (body : Core.Block) (origin : OriginId)
      (bounded : SourceFuelSize.block body ≤ cap) : TypedRangeFuelBound budget residual cfg results index low high body origin :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.block body) bounded).rangeLoop
      results index low high body origin (Nat.le_refl _)).source_mono (reflectionFuelBound_recursive_spare earlier bounded)
  have earlierEachLoop (residual : Nat) (earlier : residual < fuel) (results : List Ty) (variableId : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
      (bounded : SourceFuelSize.block body ≤ cap) : TypedEachFuelBound budget residual cfg results variableId index view byRef body origin :=
    ((fuelBoundFamily cap cfg moduleBound residual (SourceFuelSize.block body) bounded).eachLoop
      results variableId index view byRef body origin (Nat.le_refl _)).source_mono (reflectionFuelBound_recursive_spare earlier bounded)
  refine { expr := ?_, place := ?_, view := ?_, boundary := ?_, arg := ?_, block := ?_, statements := ?_, statement := ?_, whileLoop := ?_, rangeLoop := ?_, eachLoop := ?_ }
  · intro results expression nodeBound
    cases expression with
    | lit type value =>
      exact (typedExprFuelBound_lit fuel cfg results type value).source_mono leaf
    | bool value =>
      exact (typedExprFuelBound_bool fuel cfg results value).source_mono leaf
    | read place =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_read (childPlace fuel (Nat.le_refl _) results place (by omega))).source_mono
      exact spend 1 (by decide)
    | ref mode place =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_ref mode (childPlace fuel (Nat.le_refl _) results place (by omega))).source_mono
      exact spend 1 (by decide)
    | len view =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_len (childView fuel (Nat.le_refl _) results view (by omega))).source_mono
      exact spend 1 (by decide)
    | slice mode view low high origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_slice
        (childView fuel (Nat.le_refl _) results view (by omega))
        (fun residual earlier => childBoundary residual earlier results low (by omega))
        (fun residual earlier => childBoundary residual earlier results high (by omega))).source_mono
      exact spend 1 (by decide)
    | not child =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_not (childExpr fuel (Nat.le_refl _) results child (by omega))).source_mono
      exact spend 1 (by decide)
    | un operation child origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_un operation origin
        (childExpr fuel (Nat.le_refl _) results child (by omega))).source_mono
      exact spend 1 (by decide)
    | conv kind target child origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_conv kind target origin
        (childExpr fuel (Nat.le_refl _) results child (by omega))).source_mono
      exact spend 1 (by decide)
    | fill target child =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_fill target
        (childExpr fuel (Nat.le_refl _) results child (by omega))).source_mono
      exact spend 1 (by decide)
    | bin operation left right origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_bin operation origin
        (childExpr fuel (Nat.le_refl _) results left (by omega))
        (fun residual earlier => childExpr residual earlier results right (by omega))).source_mono
      exact spend 1 (by decide)
    | cmp operation left right =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_cmp operation
        (childExpr fuel (Nat.le_refl _) results left (by omega))
        (fun residual earlier => childExpr residual earlier results right (by omega))).source_mono
      exact spend 1 (by decide)
    | and left right =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_and
        (childExpr fuel (Nat.le_refl _) results left (by omega))
        (fun residual earlier => childExpr residual earlier results right (by omega))).source_mono
      exact spend 1 (by decide)
    | or left right =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_or
        (childExpr fuel (Nat.le_refl _) results left (by omega))
        (fun residual earlier => childExpr residual earlier results right (by omega))).source_mono
      exact spend 1 (by decide)
    | push owner argument origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_push origin
        (childPlace fuel (Nat.le_refl _) results owner (by omega))
        (fun residual earlier => childExpr residual earlier results argument (by omega))).source_mono
      exact spend 1 (by decide)
    | pop owner origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_pop origin
        (childPlace fuel (Nat.le_refl _) results owner (by omega))).source_mono
      exact spend 1 (by decide)
    | blockE body =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_blockE
        (childBlock fuel (Nat.le_refl _) results none [] [] true body (by omega))).source_mono
      exact spend 2 (by decide)
    | ifE condition yes no =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply (typedExprFuelBound_ifE
        (childExpr fuel (Nat.le_refl _) results condition (by omega))
        (fun residual earlier => childBlock residual earlier results none [] [] true yes (by omega))
        (fun residual earlier => childBlock residual earlier results none [] [] true no (by omega))).source_mono
      exact spend 2 (by decide)
    | arrLit target expressions =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply TypedExprFuelBound.source_mono (sourceFuel := budget + 1) ?_ (spend 1 (by decide))
      apply typedExprFuelBound_arrLit
      intro residual earlier child member
      have smaller := SourceFuelSize.exprs_member_lt member
      exact childExpr residual earlier results child (by omega)
    | structLit target expressions =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply TypedExprFuelBound.source_mono (sourceFuel := budget + 1) ?_ (spend 1 (by decide))
      apply typedExprFuelBound_structLit
      intro residual earlier child member
      have smaller := SourceFuelSize.exprs_member_lt member
      exact childExpr residual earlier results child (by omega)
    | call context arguments origin =>
      simp only [SourceFuelSize.expr] at nodeBound
      apply TypedExprFuelBound.source_mono (sourceFuel := budget + 2) ?_ (spend 2 (by decide))
      apply typedExprFuelBound_call
      · apply typedArgsFuelBound_of_children
        intro residual earlier argument member
        have smaller := SourceFuelSize.args_member_lt member
        exact (childArg residual earlier results argument (by omega)).source_mono (by omega)
      · intro bodyFuel earlier ctx impl contextAt implAt pre
        exact earlierBlock bodyFuel earlier impl.results.toList none (callPre impl) pre false impl.body
          (Nat.le_trans (moduleSyntaxCap_impl implAt) moduleBound)
  · intro results place nodeBound
    cases place with
    | var id => exact (typedPlaceFuelBound_var fuel cfg results id).source_mono leaf
    | global id => exact (typedPlaceFuelBound_global fuel cfg results id).source_mono leaf
    | deref expression =>
      simp only [SourceFuelSize.place] at nodeBound
      apply (typedPlaceFuelBound_deref (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 3 (by decide)
    | field owner index =>
      simp only [SourceFuelSize.place] at nodeBound
      apply (typedPlaceFuelBound_field (childPlace fuel (Nat.le_refl _) results owner (by omega)) index).source_mono
      exact spend 1 (by decide)
    | elem view index origin =>
      simp only [SourceFuelSize.place] at nodeBound
      apply (typedPlaceFuelBound_elem
        (childView fuel (Nat.le_refl _) results view (by omega))
        (fun residual earlier => childExpr residual earlier results index (by omega)) origin).source_mono
      exact spend 1 (by decide)
  · intro results view nodeBound
    cases view with
    | of place =>
      simp only [SourceFuelSize.view] at nodeBound
      apply (typedViewFuelBound_of (childPlace fuel (Nat.le_refl _) results place (by omega))).source_mono
      exact spend 1 (by decide)
    | val expression =>
      simp only [SourceFuelSize.view] at nodeBound
      apply (typedViewFuelBound_val (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
  · intro results boundary nodeBound
    cases boundary with
    | omitted => exact (typedBoundFuelBound_omitted fuel cfg results).source_mono leaf
    | expr expression =>
      simp only [SourceFuelSize.boundary] at nodeBound
      apply (typedBoundFuelBound_expr (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | fromEnd expression =>
      simp only [SourceFuelSize.boundary] at nodeBound
      apply (typedBoundFuelBound_fromEnd (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
  · intro results argument nodeBound
    cases argument with
    | byVal expression =>
      simp only [SourceFuelSize.arg] at nodeBound
      apply (typedArgFuelBound_byVal (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | byRef mode place =>
      simp only [SourceFuelSize.arg] at nodeBound
      apply (typedArgFuelBound_byRef mode (childPlace fuel (Nat.le_refl _) results place (by omega))).source_mono
      exact spend 1 (by decide)
  · intro results loop pre pre' want body nodeBound
    cases body with
    | mk scope statements value =>
      simp only [SourceFuelSize.block] at nodeBound
      apply TypedBlockFuelBound.source_mono (sourceFuel := budget + 1) ?_ (spend 1 (by decide))
      apply typedBlockFuelBound_mk
      · intro residual earlier
        exact childStatements residual earlier results loop statements (by omega)
      · intro residual earlier
        cases value with
        | none => trivial
        | some expression =>
          simp only [SourceFuelSize.optionalExpr] at nodeBound
          exact childExpr residual earlier results expression (by omega)
  · intro results loop statements nodeBound
    cases statements with
    | nil =>
      exact typedStatementsFuelBound_nil (by have positive := reflectionFuelBound_positive cap fuel size; omega)
    | cons head tail =>
      simp only [SourceFuelSize.stmts] at nodeBound
      apply (typedStatementsFuelBound_cons
        (childStatement fuel (Nat.le_refl _) results loop head (by omega))
        (fun residual earlier => childStatements residual earlier results loop tail (by omega))).source_mono
      exact spend 1 (by decide)
  · intro results loop statement nodeBound
    cases statement with
    | expr expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_expr
        (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | assign place expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_assign
        (childPlace fuel (Nat.le_refl _) results place (by omega))
        (fun residual earlier => childExpr residual earlier results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | clear place origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_clear
        (childPlace fuel (Nat.le_refl _) results place (by omega))).source_mono
      exact spend 1 (by decide)
    | append place view origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_append
        (childPlace fuel (Nat.le_refl _) results place (by omega))
        (fun residual earlier => childView residual earlier results view (by omega))).source_mono
      exact spend 1 (by decide)
    | popN place expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_popN
        (childPlace fuel (Nat.le_refl _) results place (by omega))
        (fun residual earlier => childExpr residual earlier results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | ifS condition yes no origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply TypedStatementFuelBound.source_mono (sourceFuel := budget + 1) ?_ (spend 1 (by decide))
      apply typedStatementFuelBound_ifS
      · exact childExpr fuel (Nat.le_refl _) results condition (by omega)
      · intro residual earlier
        exact childBlock residual earlier results loop [] [] false yes (by omega)
      · intro body present residual earlier
        have smaller := SourceFuelSize.optionalBlock_child_lt present
        exact childBlock residual earlier results loop [] [] false body (by omega)
    | «while» condition body origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_while (sourceFuel := budget) ?_).source_mono (spend 1 (by decide))
      intro residual earlier
      exact earlierWhileLoop residual earlier results condition body origin (by omega)
    | forRange index low high body origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_forRange
        (childExpr fuel (Nat.le_refl _) results low (by omega))
        (fun residual earlier => childExpr residual earlier results high (by omega))
        (fun residual earlier => earlierRangeLoop residual earlier results index low high body origin (by omega))).source_mono
      exact spend 1 (by decide)
    | forEach variableId index view byRef body origin =>
      cases view with
      | val expression =>
        simp only [SourceFuelSize.stmt,SourceFuelSize.view] at nodeBound
        apply (typedStatementFuelBound_each_value
          (childExpr fuel (Nat.le_refl _) results expression (by omega))
          (fun residual earlier => earlierEachLoop residual earlier results variableId index (.val expression) byRef body origin (by omega))).source_mono
        exact spend 2 (by decide)
      | of place =>
        simp only [SourceFuelSize.stmt,SourceFuelSize.view] at nodeBound
        apply (typedStatementFuelBound_each_place
          (childPlace fuel (Nat.le_refl _) results place (by omega))
          (fun residual earlier => earlierEachLoop residual earlier results variableId index (.of place) byRef body origin (by omega))).source_mono
        exact spend 2 (by decide)
    | ret value origin =>
      cases value with
      | none =>
        exact (typedStatementFuelBound_return_none (sourceFuel := budget)).source_mono (spend 1 (by decide))
      | some expression =>
        simp only [SourceFuelSize.stmt,SourceFuelSize.optionalExpr] at nodeBound
        apply (typedStatementFuelBound_return_some
          (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
        exact spend 1 (by decide)
    | brk origin =>
      exact (typedStatementFuelBound_break (sourceFuel := budget)).source_mono (spend 1 (by decide))
    | cont origin =>
      exact (typedStatementFuelBound_continue (sourceFuel := budget)).source_mono (spend 1 (by decide))
    | letS variableId expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_letS
        (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | rebind variableId expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_rebind
        (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | assignOp operation place expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_assignOp
        (childPlace fuel (Nat.le_refl _) results place (by omega))
        (fun residual earlier => childExpr residual earlier results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | assignWhole place expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_assignWhole
        (childPlace fuel (Nat.le_refl _) results place (by omega))
        (fun residual earlier => childExpr residual earlier results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | resize place count fill origin =>
      cases fill with
      | none =>
        simp only [SourceFuelSize.stmt,SourceFuelSize.optionalExpr] at nodeBound
        apply (typedStatementFuelBound_resize_none
          (childPlace fuel (Nat.le_refl _) results place (by omega))
          (fun residual earlier => childExpr residual earlier results count (by omega))).source_mono
        exact spend 1 (by decide)
      | some expression =>
        simp only [SourceFuelSize.stmt,SourceFuelSize.optionalExpr] at nodeBound
        apply (typedStatementFuelBound_resize_some
          (childPlace fuel (Nat.le_refl _) results place (by omega))
          (fun residual earlier => childExpr residual earlier results count (by omega))
          (fun residual earlier => childExpr residual earlier results expression (by omega))).source_mono
        exact spend 1 (by decide)
    | assertS expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_assert
        (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | abort message origin =>
      exact (typedStatementFuelBound_abort (sourceFuel := budget)).source_mono (spend 1 (by decide))
    | exit expression origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply (typedStatementFuelBound_exit
        (childExpr fuel (Nat.le_refl _) results expression (by omega))).source_mono
      exact spend 1 (by decide)
    | print arguments origin =>
      simp only [SourceFuelSize.stmt] at nodeBound
      apply TypedStatementFuelBound.source_mono (sourceFuel := budget + 2) ?_ (spend 2 (by decide))
      apply typedStatementFuelBound_print
      intro residual earlier expression member
      have smaller := SourceFuelSize.printArgs_expr_member_lt member
      exact childExpr residual earlier results expression (by omega)
  · intro results condition body origin nodeBound
    have bodyPositive := SourceFuelSize.block_pos body
    apply (typedWhileFuelBound_step
      (childExpr fuel (Nat.le_refl _) results condition (by omega)) ?_ ?_).source_mono (spend 1 (by decide))
    · intro residual earlier context
      exact earlierBlock residual earlier results (some context) [] [] false body (by omega)
    · intro residual earlier
      exact earlierWhileLoop residual earlier results condition body origin (by omega)
  · intro results index low high body origin nodeBound
    apply (typedRangeFuelBound_step (n := budget) ?_ ?_).source_mono (spend 1 (by decide))
    · intro residual earlier context pre pre'
      exact earlierBlock residual earlier results (some context) pre pre' false body (by omega)
    · intro residual earlier
      exact earlierRangeLoop residual earlier results index low high body origin (by omega)
  · intro results variableId index view byRef body origin nodeBound
    apply (typedEachFuelBound_step (sourceFuel := budget) ?_ ?_).source_mono (spend 1 (by decide))
    · intro residual earlier context pre pre'
      exact earlierBlock residual earlier results (some context) pre pre' false body (by omega)
    · intro residual earlier
      exact earlierEachLoop residual earlier results variableId index view byRef body origin (by omega)
termination_by (fuel,size)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact fuelBoundRank earlier smaller
    | exact Prod.Lex.left _ _ earlier

def loweringSourceFuelBound (module : Core.Module) (targetFuel : Nat) : Nat :=
  reflectionFuelBound (moduleSyntaxCap module) targetFuel (moduleSyntaxCap module) + 1

theorem acceptedModule_fuelBound {cfg : Cfg}
    (accepted : Core.validate cfg.mod = .ok ()) (targetFuel : Nat) :
    FuelBoundM (loweringSourceFuelBound cfg.mod targetFuel) targetFuel
      (fun n => Core.runModule n cfg)
      (fun n => GIR.runModule n ⟨cfg.profile,lower cfg.mod⟩) St.initial := by
  unfold loweringSourceFuelBound
  apply typedModule_fuelBound accepted
  · intro residual equal id global lookup
    have family := fuelBoundFamily (moduleSyntaxCap cfg.mod) cfg (Nat.le_refl _) residual
      (moduleSyntaxCap cfg.mod) (Nat.le_refl _)
    apply (family.expr [global.ty] global.init (moduleSyntaxCap_global lookup)).source_mono
    have enough := reflectionFuelBound_target_mono (syntaxCap := moduleSyntaxCap cfg.mod)
      (nodeSize := moduleSyntaxCap cfg.mod) (show residual ≤ targetFuel by omega)
    omega
  · intro residual equal context impl contextAt implAt
    have family := fuelBoundFamily (moduleSyntaxCap cfg.mod) cfg (Nat.le_refl _) residual
      (moduleSyntaxCap cfg.mod) (Nat.le_refl _)
    apply (family.block impl.results.toList none (callPre impl) [] false impl.body
      (moduleSyntaxCap_impl implAt)).source_mono
    exact reflectionFuelBound_target_mono (by omega)

end Goose.Lower
