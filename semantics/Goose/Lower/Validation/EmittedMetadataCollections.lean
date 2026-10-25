import Goose.Lower.Validation.EmittedMetadataAccess
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedMetadataSourceBound (env : Core.TEnv) (results : List Ty) (bound : Bound) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerBound bound)

def EmittedMetadataSourceArgument (env : Core.TEnv) (results : List Ty) : Arg → Prop
  | .byVal expr => EmittedMetadataSourceExpression env results expr
  | .byRef _ place => EmittedMetadataSourcePlace env results place

theorem metadata_source_bound_omitted (env : Core.TEnv) (results : List Ty) :
    EmittedMetadataSourceBound env results .omitted := by
  intro agreement start finish source
  exact (EmittedMetadataAction.pure _ none Bnd.omitted).metadata

theorem metadata_source_bound_expr {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourceBound env results (.expr expr) := by
  intro agreement start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.pure _ none (Bnd.val value)).metadata

theorem metadata_source_bound_fromEnd {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourceBound env results (.fromEnd expr) := by
  intro agreement start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.pure _ none (Bnd.fromEnd value)).metadata

theorem metadata_source_slice {env : Core.TEnv} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : EmittedMetadataSourceView env results view) (lowChild : EmittedMetadataSourceBound env results lo)
    (highChild : EmittedMetadataSourceBound env results hi) :
    EmittedMetadataSourceExpression env results (.slice requested view lo hi origin) := by
  intro agreement type start finish source
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, lowSource, highSource, _⟩ :=
    tyExpr_slice_children source
  exact ((EmittedMetadataAction.lowerView view (viewChild agreement viewSource)).bind fun vw =>
    (EmittedMetadataAction.lowerBound lo (lowChild agreement lowSource)).bind fun low =>
      (EmittedMetadataAction.lowerBound hi (highChild agreement highSource)).bind fun high =>
        EmittedMetadataAction.emitDef _ none (.viewSlice requested vw low high (some origin))
         ).metadata

theorem metadata_source_expressions {env : Core.TEnv} {results : List Ty} (exprs : List Expr)
    (agreement : EmittedMetadataResultTypes env results)
    {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (children : ∀ expr ∈ exprs, EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerExprs exprs) := by
  induction exprs generalizing types start with
  | nil => exact (EmittedMetadataAction.pure _ none []).metadata
  | cons expr rest inductionHypothesis =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      obtain ⟨actual, middle, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases same : (actual == type) = true
      · simp only [same, ite_true] at source
        exact ((EmittedMetadataAction.lowerExpr expr (children expr (by simp) agreement childSource)).bind fun value =>
          (EmittedMetadataAction.lowerExprs rest (inductionHypothesis source
            (fun e member => children e (by simp [member])))).bind fun values =>
              EmittedMetadataAction.pure _ none (value :: values)).metadata
      · simp [same, chk] at source

theorem metadata_source_arrayLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceExpression env results (.arrLit type exprs) := by
  intro agreement result start finish source
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  exact ((EmittedMetadataAction.lowerExprs exprs (metadata_source_expressions exprs agreement
    (tyExprsAs_structExprs childSource) children)).bind fun values =>
      EmittedMetadataAction.emitDef _ none (.arrLit type values)).metadata

theorem metadata_source_structLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceExpression env results (.structLit type exprs) := by
  intro agreement result start finish source
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ := tyExpr_structLiteral_children source
  exact ((EmittedMetadataAction.lowerExprs exprs (metadata_source_expressions exprs agreement childSource children)).bind fun values =>
    EmittedMetadataAction.emitDef _ none (.structLit type values)).metadata

theorem metadata_source_fill {env : Core.TEnv} {results : List Ty} (type : Ty) (expr : Expr)
    (child : EmittedMetadataSourceExpression env results expr) : EmittedMetadataSourceExpression env results (.fill type expr) := by
  intro agreement result start finish source
  obtain ⟨_, element, count, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.arrFill type value)).metadata

theorem metadata_source_pop {env : Core.TEnv} {results : List Ty} (owner : Place) (origin : OriginId)
    (child : EmittedMetadataSourcePlace env results owner) : EmittedMetadataSourceExpression env results (.pop owner origin) := by
  intro agreement result start finish source
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  exact ((EmittedMetadataAction.lowerPlace owner (child agreement ownerSource)).bind fun value =>
    EmittedMetadataAction.emitDef _ none (.pop value (some origin))).metadata

theorem metadata_source_push {env : Core.TEnv} {results : List Ty} (owner : Place) (expr : Expr) (origin : Option OriginId)
    (placeChild : EmittedMetadataSourcePlace env results owner) (exprChild : EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceExpression env results (.push owner expr origin) := by
  intro agreement result start finish source
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerSource, shape, childSource, _⟩ :=
    tyExpr_push_children source
  exact ((EmittedMetadataAction.lowerPlace owner (placeChild agreement ownerSource)).bind fun ownerValue =>
    (EmittedMetadataAction.lowerExpr expr (exprChild agreement childSource)).bind fun value =>
      EmittedMetadataAction.emitDef _ none (.push ownerValue value origin)).metadata

theorem metadata_source_arguments {env : Core.TEnv} {results : List Ty} (args : List Arg)
    (agreement : EmittedMetadataResultTypes env results)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (children : ∀ arg ∈ args, EmittedMetadataSourceArgument env results arg) :
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerArgs args) := by
  induction args generalizing params start with
  | nil => exact (EmittedMetadataAction.pure _ none []).metadata
  | cons arg args inductionHypothesis =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      have restLength : params.length = args.length := by simpa using sameLength
      cases arg with
      | byVal expr =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
          tyArgs_byVal_head source
        have child : EmittedMetadataSourceExpression env results expr := children (.byVal expr) (by simp)
        exact ((EmittedMetadataAction.lowerExpr expr (child agreement childSource)).bind fun value =>
          (EmittedMetadataAction.lowerArgs args (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member])))).bind fun values =>
              EmittedMetadataAction.pure _ none (value :: values)).metadata
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        have child : EmittedMetadataSourcePlace env results place := children (.byRef mu place) (by simp)
        have argument : EmittedMetadataAction (lowerEnv env.mod env.vars results) none (lowerArg (.byRef mu place)) :=
          (EmittedMetadataAction.lowerPlace place (child agreement placeSource)).bind fun value => EmittedMetadataAction.borrowTo _ none mu value
        exact (argument.bind fun value =>
          (EmittedMetadataAction.lowerArgs args (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member])))).bind fun values =>
              EmittedMetadataAction.pure _ none (value :: values)).metadata

theorem metadata_source_call {env : Core.TEnv} {results : List Ty} (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, EmittedMetadataSourceArgument env results arg) :
    EmittedMetadataSourceExpression env results (.call context args origin) := by
  intro agreement type start finish source
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt, length, argsSource, resultSource⟩ :=
    tyExpr_call_tables source
  apply EmittedMetadataAction.metadata
  refine (EmittedMetadataAction.lowerArgs args (metadata_source_arguments args agreement length argsSource children)).bind fun values =>
    (EmittedMetadataAction.emitDef _ none (.call context values (some origin))).bind fun value =>
      (EmittedMetadataAction.read _ none).bind fun reader => ?_
  cases reader.mod.noReturn context
  · exact EmittedMetadataAction.pure _ none value
  · exact (EmittedMetadataAction.emitNoSuccessors _ none .unreachable rfl (fun _ _ _ => .unreachable)).bind fun _ => EmittedMetadataAction.pure _ none value

end Goose.Lower.Validation
