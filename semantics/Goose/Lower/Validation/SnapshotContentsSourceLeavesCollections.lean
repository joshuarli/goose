import Goose.Lower.Validation.SnapshotContentsSourceLeavesAccess
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def SnapshotSourceBound (env : Core.TEnv) (results : List Ty) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerBound bound)

def SnapshotSourceArgument (env : Core.TEnv) (results : List Ty) : Arg → Prop
  | .byVal expr => SnapshotSourceExpression env results expr
  | .byRef _ place => SnapshotSourcePlace env results place

theorem snapshot_source_bound_omitted (env : Core.TEnv) (results : List Ty) :
    SnapshotSourceBound env results .omitted := by
  intro start finish source
  exact SnapshotTraceRun.pure Bnd.omitted

theorem snapshot_source_bound_expr {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceBound env results (.expr expr) := by
  intro start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    SnapshotSourceAction.pure _ none (Bnd.val value)).snapshots

theorem snapshot_source_bound_fromEnd {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceBound env results (.fromEnd expr) := by
  intro start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    SnapshotSourceAction.pure _ none (Bnd.fromEnd value)).snapshots

theorem snapshot_source_slice {env : Core.TEnv} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : SnapshotSourceView env results view) (lowChild : SnapshotSourceBound env results lo)
    (highChild : SnapshotSourceBound env results hi) :
    SnapshotSourceExpression env results (.slice requested view lo hi origin) := by
  intro type start finish source
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, lowSource, highSource, _⟩ :=
    tyExpr_slice_children source
  exact ((SnapshotSourceAction.lowerView view (viewChild viewSource)).bind fun vw =>
    (SnapshotSourceAction.lowerBound lo (lowChild lowSource)).bind fun low =>
      (SnapshotSourceAction.lowerBound hi (highChild highSource)).bind fun high =>
        SnapshotSourceAction.emitDef _ none (.viewSlice requested vw low high (some origin))
          (by intros; intro h; cases h)).snapshots

theorem snapshot_source_expressions {env : Core.TEnv} {results : List Ty} (exprs : List Expr)
    {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (children : ∀ expr ∈ exprs, SnapshotSourceExpression env results expr) :
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerExprs exprs) := by
  induction exprs generalizing types start with
  | nil => exact SnapshotTraceRun.pure []
  | cons expr rest inductionHypothesis =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      obtain ⟨actual, middle, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases same : (actual == type) = true
      · simp only [same, ite_true] at source
        exact ((SnapshotSourceAction.lowerExpr expr (children expr (by simp) childSource)).bind fun value =>
          (SnapshotSourceAction.lowerExprs rest (inductionHypothesis source
            (fun e member => children e (by simp [member])))).bind fun values =>
              SnapshotSourceAction.pure _ none (value :: values)).snapshots
      · simp [same, chk] at source

theorem snapshot_source_arrayLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, SnapshotSourceExpression env results expr) :
    SnapshotSourceExpression env results (.arrLit type exprs) := by
  intro result start finish source
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  exact ((SnapshotSourceAction.lowerExprs exprs (snapshot_source_expressions exprs
    (tyExprsAs_structExprs childSource) children)).bind fun values =>
      SnapshotSourceAction.emitDef _ none (.arrLit type values) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_structLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, SnapshotSourceExpression env results expr) :
    SnapshotSourceExpression env results (.structLit type exprs) := by
  intro result start finish source
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ := tyExpr_structLiteral_children source
  exact ((SnapshotSourceAction.lowerExprs exprs (snapshot_source_expressions exprs childSource children)).bind fun values =>
    SnapshotSourceAction.emitDef _ none (.structLit type values) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_fill {env : Core.TEnv} {results : List Ty} (type : Ty) (expr : Expr)
    (child : SnapshotSourceExpression env results expr) : SnapshotSourceExpression env results (.fill type expr) := by
  intro result start finish source
  obtain ⟨_, element, count, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.arrFill type value) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_pop {env : Core.TEnv} {results : List Ty} (owner : Place) (origin : OriginId)
    (child : SnapshotSourcePlace env results owner) : SnapshotSourceExpression env results (.pop owner origin) := by
  intro result start finish source
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  exact ((SnapshotSourceAction.lowerPlace owner (child ownerSource)).bind fun value =>
    SnapshotSourceAction.emitDef _ none (.pop value (some origin)) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_push {env : Core.TEnv} {results : List Ty} (owner : Place) (expr : Expr) (origin : Option OriginId)
    (placeChild : SnapshotSourcePlace env results owner) (exprChild : SnapshotSourceExpression env results expr) :
    SnapshotSourceExpression env results (.push owner expr origin) := by
  intro result start finish source
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerSource, shape, childSource, _⟩ :=
    tyExpr_push_children source
  exact ((SnapshotSourceAction.lowerPlace owner (placeChild ownerSource)).bind fun ownerValue =>
    (SnapshotSourceAction.lowerExpr expr (exprChild childSource)).bind fun value =>
      SnapshotSourceAction.emitDef _ none (.push ownerValue value origin) (by intros; intro h; cases h)).snapshots

theorem snapshot_source_arguments {env : Core.TEnv} {results : List Ty} (args : List Arg)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (children : ∀ arg ∈ args, SnapshotSourceArgument env results arg) :
    SnapshotTraceRun (lowerEnv env.mod env.vars results) none (lowerArgs args) := by
  induction args generalizing params start with
  | nil => exact SnapshotTraceRun.pure []
  | cons arg args inductionHypothesis =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      have restLength : params.length = args.length := by simpa using sameLength
      cases arg with
      | byVal expr =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
          tyArgs_byVal_head source
        have child : SnapshotSourceExpression env results expr := children (.byVal expr) (by simp)
        exact ((SnapshotSourceAction.lowerExpr expr (child childSource)).bind fun value =>
          (SnapshotSourceAction.lowerArgs args (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member])))).bind fun values =>
              SnapshotSourceAction.pure _ none (value :: values)).snapshots
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        have child : SnapshotSourcePlace env results place := children (.byRef mu place) (by simp)
        have argument : SnapshotSourceAction (lowerEnv env.mod env.vars results) none (lowerArg (.byRef mu place)) :=
          (SnapshotSourceAction.lowerPlace place (child placeSource)).bind fun value => SnapshotSourceAction.borrowTo _ none mu value
        exact (argument.bind fun value =>
          (SnapshotSourceAction.lowerArgs args (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member])))).bind fun values =>
              SnapshotSourceAction.pure _ none (value :: values)).snapshots

theorem snapshot_source_call {env : Core.TEnv} {results : List Ty} (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, SnapshotSourceArgument env results arg) :
    SnapshotSourceExpression env results (.call context args origin) := by
  intro type start finish source
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt, length, argsSource, resultSource⟩ :=
    tyExpr_call_tables source
  apply SnapshotSourceAction.snapshots
  refine (SnapshotSourceAction.lowerArgs args (snapshot_source_arguments args length argsSource children)).bind fun values =>
    (SnapshotSourceAction.emitDef _ none (.call context values (some origin)) (by intros; intro h; cases h)).bind fun value =>
      (SnapshotSourceAction.read _ none).bind fun reader => ?_
  cases reader.mod.noReturn context
  · exact SnapshotSourceAction.pure _ none value
  · exact (SnapshotSourceAction.emitTerm _ none .unreachable rfl).bind fun _ => SnapshotSourceAction.pure _ none value

end Goose.Lower.Validation
