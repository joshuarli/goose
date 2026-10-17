import Goose.Lower.EachStatic
import Goose.Lower.ReflectionTypedAggregates
import Goose.Lower.ReflectionWrites
import Goose.Lower.ReflectionResize
import Goose.Lower.ReflectionBindings
import Goose.Lower.ReflectionOutput
import Goose.Lower.ReflectionTransfers
import Goose.Lower.ReflectionModule
import Goose.Lower.ReflectionCallExpressions
import Goose.Lower.ReflectionBranchesStatements
import Goose.Lower.ReflectionMemoryExpressions
import Goose.Lower.ReflectionTypedMutations
import Goose.Lower.ReflectionIterations
import Goose.Lower.ReflectionWhile

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem reflectionRank {fuel residual size smaller : Nat}
    (bound : residual ≤ fuel) (child : smaller < size) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (residual,smaller) (fuel,size) := by
  rcases Nat.lt_or_eq_of_le bound with less | rfl
  · exact Prod.Lex.left _ _ less
  · exact Prod.Lex.right _ child

mutual

theorem typedExpr_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (expression : Expr) : TypedExprReflection fuel cfg results expression := by
  cases expression with
  | lit type value => exact typedExprReflection_lit fuel cfg results type value
  | bool value => exact typedExprReflection_bool fuel cfg results value
  | read place => exact typedExprReflection_read (typedPlace_reflection fuel cfg results place)
  | ref mode place => exact typedExprReflection_ref mode (typedPlace_reflection fuel cfg results place)
  | len view => exact typedExprReflection_len (typedView_reflection fuel cfg results view)
  | slice mode view low high origin =>
    exact typedExprReflection_slice (typedView_reflection fuel cfg results view)
      (fun residual bound => typedBound_reflection residual cfg results low)
      (fun residual bound => typedBound_reflection residual cfg results high)
  | not expression => exact typedExprReflection_not (typedExpr_reflection fuel cfg results expression)
  | un operation expression origin =>
    exact typedExprReflection_un operation origin (typedExpr_reflection fuel cfg results expression)
  | conv kind target expression origin =>
    exact typedExprReflection_conv kind target origin (typedExpr_reflection fuel cfg results expression)
  | fill target expression =>
    exact typedExprReflection_fill target (typedExpr_reflection fuel cfg results expression)
  | bin operation left right origin =>
    exact typedExprReflection_bin operation origin (typedExpr_reflection fuel cfg results left)
      (fun residual bound => typedExpr_reflection residual cfg results right)
  | cmp operation left right =>
    exact typedExprReflection_cmp operation (typedExpr_reflection fuel cfg results left)
      (fun residual bound => typedExpr_reflection residual cfg results right)
  | and left right =>
    exact typedExprReflection_and (typedExpr_reflection fuel cfg results left)
      (fun residual bound => typedExpr_reflection residual cfg results right)
  | or left right =>
    exact typedExprReflection_or (typedExpr_reflection fuel cfg results left)
      (fun residual bound => typedExpr_reflection residual cfg results right)
  | push owner argument origin =>
    exact typedExprReflection_push origin (typedPlace_reflection fuel cfg results owner)
      (fun residual bound => typedExpr_reflection residual cfg results argument)
  | pop owner origin =>
    exact typedExprReflection_pop origin (typedPlace_reflection fuel cfg results owner)
  | blockE body =>
    exact typedExprReflection_blockE (typedBlock_reflection fuel cfg results none [] [] true body)
  | ifE condition yes no =>
    exact typedExprReflection_ifE (typedExpr_reflection fuel cfg results condition)
      (fun residual bound => typedBlock_reflection residual cfg results none [] [] true yes)
      (fun residual bound => typedBlock_reflection residual cfg results none [] [] true no)
  | arrLit target expressions =>
    apply typedExprReflection_arrLit
    intro residual bound child member
    exact typedExpr_reflection residual cfg results child
  | structLit target expressions =>
    apply typedExprReflection_structLit
    intro residual bound child member
    exact typedExpr_reflection residual cfg results child
  | call context arguments origin =>
    apply typedExprReflection_call
    · apply typedArgsReflection_of_children
      intro residual bound argument member
      exact typedArg_reflection residual cfg results argument
    · intro bodyFuel bound ctx impl contextAt implAt pre
      exact typedBlock_reflection bodyFuel cfg impl.results.toList none (callPre impl) pre false impl.body
termination_by (fuel,sizeOf expression)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial | skip
  all_goals
    have memberSize := List.sizeOf_lt_of_mem ‹_ ∈ _›
    exact reflectionRank (by omega) (by omega)

theorem typedPlace_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (place : Place) : TypedPlaceReflection fuel cfg results place := by
  cases place with
  | var id => exact typedPlaceReflection_var fuel cfg results id
  | global id => exact typedPlaceReflection_global fuel cfg results id
  | deref expression => exact typedPlaceReflection_deref (typedExpr_reflection fuel cfg results expression)
  | field owner index => exact typedPlaceReflection_field (typedPlace_reflection fuel cfg results owner) index
  | elem view index origin =>
    exact typedPlaceReflection_elem (typedView_reflection fuel cfg results view)
      (fun residual bound => typedExpr_reflection residual cfg results index) origin
termination_by (fuel,sizeOf place)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedView_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (view : View) : TypedViewReflection fuel cfg results view := by
  cases view with
  | of place => exact typedViewReflection_of (typedPlace_reflection fuel cfg results place)
  | val expression => exact typedViewReflection_val (typedExpr_reflection fuel cfg results expression)
termination_by (fuel,sizeOf view)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedBound_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (bound : Bound) : TypedBoundReflection fuel cfg results bound := by
  cases bound with
  | expr expression => exact typedBoundReflection_expr (typedExpr_reflection fuel cfg results expression)
  | fromEnd expression => exact typedBoundReflection_fromEnd (typedExpr_reflection fuel cfg results expression)
  | omitted => exact typedBoundReflection_omitted fuel cfg results
termination_by (fuel,sizeOf bound)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedArg_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (argument : Arg) : TypedArgReflection fuel cfg results argument := by
  cases argument with
  | byVal expression => exact typedArgReflection_byVal (typedExpr_reflection fuel cfg results expression)
  | byRef mode place => exact typedArgReflection_byRef mode (typedPlace_reflection fuel cfg results place)
termination_by (fuel,sizeOf argument)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedBlock_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (body : Core.Block) :
    TypedBlockReflection fuel cfg results loop pre pre' want body := by
  cases body with
  | mk scope statements value =>
    apply typedBlockReflection_mk
    · intro residual bound
      exact typedStatements_reflection residual cfg results loop statements
    · intro residual bound
      cases value with
      | none => trivial
      | some expression => exact typedExpr_reflection residual cfg results expression
termination_by (fuel,sizeOf body)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedStatements_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (loop : Option LoopCtx) (statements : List Stmt) :
    TypedStatementsReflection fuel cfg results loop statements := by
  cases statements with
  | nil => exact typedStatementsReflection_nil fuel cfg results loop
  | cons head tail =>
    exact typedStatementsReflection_cons (typedStatement_reflection fuel cfg results loop head)
      (fun residual bound => typedStatements_reflection residual cfg results loop tail)
termination_by (fuel,sizeOf statements)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial

theorem typedStatement_reflection (fuel : Nat) (cfg : Cfg)
    (results : List Ty) (loop : Option LoopCtx) (statement : Stmt) :
    TypedStatementReflection fuel cfg results loop statement := by
  cases statement with
  | expr expression origin => exact typedStatementReflection_expr origin (typedExpr_reflection fuel cfg results expression)
  | assign place expression origin =>
    exact typedStatementReflection_assign (typedPlace_reflection fuel cfg results place)
      (fun residual bound => typedExpr_reflection residual cfg results expression)
  | clear place origin => exact typedStatementReflection_clear (typedPlace_reflection fuel cfg results place)
  | append place view origin =>
    exact typedStatementReflection_append (typedPlace_reflection fuel cfg results place)
      (fun residual bound => typedView_reflection residual cfg results view)
  | popN place expression origin =>
    exact typedStatementReflection_popN (typedPlace_reflection fuel cfg results place)
      (fun residual bound => typedExpr_reflection residual cfg results expression)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      exact typedStatementReflection_if_none (typedExpr_reflection fuel cfg results condition)
        (fun residual bound => typedBlock_reflection residual cfg results loop [] [] false yes)
    | some no =>
      exact typedStatementReflection_if_some (typedExpr_reflection fuel cfg results condition)
        (fun residual bound => typedBlock_reflection residual cfg results loop [] [] false yes)
        (fun residual bound => typedBlock_reflection residual cfg results loop [] [] false no)
  | «while» condition body origin =>
    apply typedStatementReflection_while
    intro residual bound
    apply typedWhileReflection_of_children
    · intro remaining smaller
      exact typedExpr_reflection remaining cfg results condition
    · intro remaining smaller context
      exact typedBlock_reflection remaining cfg results (some context) [] [] false body
  | forRange index low high body origin =>
    apply typedStatementReflection_range (typedExpr_reflection fuel cfg results low)
      (fun residual bound => typedExpr_reflection residual cfg results high)
    intro residual bound
    apply typedRangeReflection_of_children
    intro remaining smaller context pre pre'
    exact typedBlock_reflection remaining cfg results (some context) pre pre' false body
  | forEach variableId index view byRef body origin =>
    cases view with
    | val expression =>
      apply typedStatementReflection_each_value (typedExpr_reflection fuel cfg results expression)
      intro residual bound
      apply typedEachReflection_of_children
      intro remaining smaller context pre pre'
      exact typedBlock_reflection remaining cfg results (some context) pre pre' false body
    | of place =>
      apply typedStatementReflection_each_place (typedPlace_reflection fuel cfg results place) (placeOwnerShape_generated cfg results place)
      intro residual bound
      apply typedEachReflection_of_children
      intro remaining smaller context pre pre'
      exact typedBlock_reflection remaining cfg results (some context) pre pre' false body
  | ret value origin =>
    cases value with
    | none => exact typedStatementReflection_return_none
    | some expression => exact typedStatementReflection_return_some (typedExpr_reflection fuel cfg results expression)
  | brk origin => exact typedStatementReflection_break
  | cont origin => exact typedStatementReflection_continue
  | letS variableId expression origin =>
    exact typedStatementReflection_letS (typedExpr_reflection fuel cfg results expression)
  | rebind variableId expression origin =>
    exact typedStatementReflection_rebind (typedExpr_reflection fuel cfg results expression)
  | assignOp operation place expression origin =>
    exact typedStatementReflection_assignOp (typedPlace_reflection fuel cfg results place)
      (fun residual bound => typedExpr_reflection residual cfg results expression)
  | assignWhole place expression origin =>
    exact typedStatementReflection_assignWhole (typedPlace_reflection fuel cfg results place)
      (fun residual bound => typedExpr_reflection residual cfg results expression)
  | resize place size fill origin =>
    cases fill with
    | none =>
      exact typedStatementReflection_resize_none (typedPlace_reflection fuel cfg results place)
        (fun residual bound => typedExpr_reflection residual cfg results size)
    | some expression =>
      exact typedStatementReflection_resize_some (typedPlace_reflection fuel cfg results place)
        (fun residual bound => typedExpr_reflection residual cfg results size)
        (fun residual bound => typedExpr_reflection residual cfg results expression)
  | assertS expression origin =>
    exact typedStatementReflection_assert (typedExpr_reflection fuel cfg results expression)
  | abort message origin => exact typedStatementReflection_abort
  | exit expression origin =>
    exact typedStatementReflection_exit (typedExpr_reflection fuel cfg results expression)
  | print arguments origin =>
    apply typedStatementReflection_print
    intro residual bound expression member
    exact typedExpr_reflection residual cfg results expression
termination_by (fuel,sizeOf statement)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | decreasing_trivial | skip
  all_goals
    have memberSize := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp only [PrintArg.expr.sizeOf_spec] at memberSize
    exact reflectionRank (by omega) (by omega)

end

theorem acceptedModule_reflection {cfg : Cfg}
    (accepted : Core.validate cfg.mod = .ok ()) :
    ReflectM (fun n => Core.runModule n cfg)
      (fun n => GIR.runModule n ⟨cfg.profile,lower cfg.mod⟩) St.initial := by
  intro fuel
  apply typedModule_reflection accepted
  · intro residual equal id global globalAt
    exact typedExpr_reflection residual cfg [global.ty] global.init
  · intro bodyFuel equal context impl contextAt implAt
    exact typedBlock_reflection bodyFuel cfg impl.results.toList none (callPre impl) [] false impl.body

theorem acceptedModule_never_faults {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : NumProfile) :
    ∀ fuel kind, GIR.run fuel profile (lower module) ≠ .fault kind :=
  reflected_lowering_never_faults accepted profile (acceptedModule_reflection accepted)

end Goose.Lower
