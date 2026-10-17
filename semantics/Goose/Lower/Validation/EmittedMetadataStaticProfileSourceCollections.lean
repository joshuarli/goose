import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceAccess
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedProfileSourceBound (env : Core.TEnv) (results : List Ty) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerBound bound)

def EmittedProfileSourceArgument (env : Core.TEnv) (results : List Ty) : Arg → Prop
  | .byVal expr => EmittedProfileSourceExpression env results expr
  | .byRef _ place => EmittedProfileSourcePlace env results place

theorem profile_source_bound_omitted (env : Core.TEnv) (results : List Ty) :
    EmittedProfileSourceBound env results .omitted := by
  intro start finish source
  exact (EmittedProfileRun.pure Bnd.omitted)

theorem profile_source_bound_expr {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceBound env results (.expr expr) := by
  intro start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.pure (Bnd.val value))

theorem profile_source_bound_fromEnd {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceBound env results (.fromEnd expr) := by
  intro start finish source
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.pure (Bnd.fromEnd value))

theorem profile_source_slice {env : Core.TEnv} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : EmittedProfileSourceView env results view) (lowChild : EmittedProfileSourceBound env results lo)
    (highChild : EmittedProfileSourceBound env results hi) :
    EmittedProfileSourceExpression env results (.slice requested view lo hi origin) := by
  intro type start finish source
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, lowSource, highSource, _⟩ :=
    tyExpr_slice_children source
  exact ((viewChild viewSource).bind fun vw =>
    (lowChild lowSource).bind fun low =>
      (highChild highSource).bind fun high =>
        EmittedProfileRun.emitDef (.viewSlice requested vw low high (some origin)) (by intro; trivial)
         )

theorem profile_source_expressions {env : Core.TEnv} {results : List Ty} (exprs : List Expr)
    {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (children : ∀ expr ∈ exprs, EmittedProfileSourceExpression env results expr) :
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerExprs exprs) := by
  induction exprs generalizing types start with
  | nil => exact (EmittedProfileRun.pure [])
  | cons expr rest inductionHypothesis =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      obtain ⟨actual, middle, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases same : (actual == type) = true
      · simp only [same, ite_true] at source
        exact ((children expr (by simp) childSource).bind fun value =>
          (inductionHypothesis source
            (fun e member => children e (by simp [member]))).bind fun values =>
              EmittedProfileRun.pure (value :: values))
      · simp [same, chk] at source

theorem profile_source_arrayLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceExpression env results (.arrLit type exprs) := by
  intro result start finish source
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  exact ((profile_source_expressions exprs
    (tyExprsAs_structExprs childSource) children).bind fun values =>
      EmittedProfileRun.emitDef (.arrLit type values) (by intro; trivial))

theorem profile_source_structLiteral {env : Core.TEnv} {results : List Ty} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceExpression env results (.structLit type exprs) := by
  intro result start finish source
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ := tyExpr_structLiteral_children source
  exact ((profile_source_expressions exprs childSource children).bind fun values =>
    EmittedProfileRun.emitDef (.structLit type values) (by intro; trivial))

theorem profile_source_fill {env : Core.TEnv} {results : List Ty} (type : Ty) (expr : Expr)
    (child : EmittedProfileSourceExpression env results expr) : EmittedProfileSourceExpression env results (.fill type expr) := by
  intro result start finish source
  obtain ⟨_, element, count, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  exact ((child childSource).bind fun value =>
    EmittedProfileRun.emitDef (.arrFill type value) (by intro; trivial))

theorem profile_source_pop {env : Core.TEnv} {results : List Ty} (owner : Place) (origin : OriginId)
    (child : EmittedProfileSourcePlace env results owner) : EmittedProfileSourceExpression env results (.pop owner origin) := by
  intro result start finish source
  have profile := static_tyExpr_pop_profile source
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  exact ((child ownerSource).bind fun value =>
    EmittedProfileRun.emitDef (.pop value (some origin)) (fun _ => profile))

theorem profile_source_push {env : Core.TEnv} {results : List Ty} (owner : Place) (expr : Expr) (origin : Option OriginId)
    (placeChild : EmittedProfileSourcePlace env results owner) (exprChild : EmittedProfileSourceExpression env results expr) :
    EmittedProfileSourceExpression env results (.push owner expr origin) := by
  intro result start finish source
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerSource, shape, childSource, _⟩ :=
    tyExpr_push_children source
  exact ((placeChild ownerSource).bind fun ownerValue =>
    (exprChild childSource).bind fun value =>
      EmittedProfileRun.emitDef (.push ownerValue value origin) (by intro; trivial))

theorem profile_source_arguments {env : Core.TEnv} {results : List Ty} (args : List Arg)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (children : ∀ arg ∈ args, EmittedProfileSourceArgument env results arg) :
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerArgs args) := by
  induction args generalizing params start with
  | nil => exact (EmittedProfileRun.pure [])
  | cons arg args inductionHypothesis =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      have restLength : params.length = args.length := by simpa using sameLength
      cases arg with
      | byVal expr =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
          tyArgs_byVal_head source
        have child : EmittedProfileSourceExpression env results expr := children (.byVal expr) (by simp)
        exact ((child childSource).bind fun value =>
          (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member]))).bind fun values =>
              EmittedProfileRun.pure (value :: values))
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        have child : EmittedProfileSourcePlace env results place := children (.byRef mu place) (by simp)
        have argument : EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerArg (.byRef mu place)) :=
          (child placeSource).bind fun value => EmittedProfileRun.borrowTo mu value
        exact (argument.bind fun value =>
          (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member]))).bind fun values =>
              EmittedProfileRun.pure (value :: values))

theorem profile_source_call {env : Core.TEnv} {results : List Ty} (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, EmittedProfileSourceArgument env results arg) :
    EmittedProfileSourceExpression env results (.call context args origin) := by
  intro type start finish source
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt, length, argsSource, resultSource⟩ :=
    tyExpr_call_tables source
  refine (profile_source_arguments args length argsSource children).bind fun values =>
    (EmittedProfileRun.emitDef (.call context values (some origin)) (by intro; trivial)).bind fun value =>
      (EmittedProfileRun.read).bind fun reader => ?_
  cases reader.mod.noReturn context
  · exact EmittedProfileRun.pure value
  · exact (EmittedProfileRun.emitTerm .unreachable trivial).bind fun _ => EmittedProfileRun.pure value

end Goose.Lower.Validation
