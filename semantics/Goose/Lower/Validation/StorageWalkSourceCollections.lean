import Goose.Lower.Validation.StorageWalkSourceAccess
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_bound_omitted (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) :
    StorageWalkSourceBound env results stack .omitted := by
  intro start finish source visible loop
  exact (StorageWalkAction.pure _ stack loop Bnd.omitted)

theorem storageWalk_source_bound_expr {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (expr : Expr)
    (child : StorageWalkSourceExpression env results stack expr) : StorageWalkSourceBound env results stack (.expr expr) := by
  intro start finish source visible loop
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((child childSource visible loop).bind fun value =>
    StorageWalkAction.pure _ stack loop (Bnd.val value))

theorem storageWalk_source_bound_fromEnd {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (expr : Expr)
    (child : StorageWalkSourceExpression env results stack expr) : StorageWalkSourceBound env results stack (.fromEnd expr) := by
  intro start finish source visible loop
  obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
  exact ((child childSource visible loop).bind fun value =>
    StorageWalkAction.pure _ stack loop (Bnd.fromEnd value))

theorem storageWalk_source_slice {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : StorageWalkSourceView env results stack view) (lowChild : StorageWalkSourceBound env results stack lo)
    (highChild : StorageWalkSourceBound env results stack hi) :
    StorageWalkSourceExpression env results stack (.slice requested view lo hi origin) := by
  intro type start finish source visible loop
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, lowSource, highSource, _⟩ :=
    tyExpr_slice_children source
  exact ((viewChild viewSource visible loop).bind fun vw =>
    (lowChild lowSource visible loop).bind fun low =>
      (highChild highSource visible loop).bind fun high =>
        StorageWalkAction.emitDef _ stack loop (.viewSlice requested vw low high (some origin)) (by simp [StorageInstructionVisible])
         )

theorem storageWalk_source_expressions {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (exprs : List Expr)
    (visible : StorageWalkVisible env stack) (loop : Option LoopCtx)
    {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (children : ∀ expr ∈ exprs, StorageWalkSourceExpression env results stack expr) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerExprs exprs) := by
  induction exprs generalizing types start with
  | nil => exact (StorageWalkAction.pure _ stack loop [])
  | cons expr rest inductionHypothesis =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      obtain ⟨actual, middle, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases same : (actual == type) = true
      · simp only [same, ite_true] at source
        exact ((children expr (by simp) childSource visible loop).bind fun value =>
          (inductionHypothesis source
            (fun e member => children e (by simp [member]))).bind fun values =>
              StorageWalkAction.pure _ stack loop (value :: values))
      · simp [same, chk] at source

theorem storageWalk_source_arrayLiteral {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceExpression env results stack (.arrLit type exprs) := by
  intro result start finish source visible loop
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  exact ((storageWalk_source_expressions exprs visible loop
    (tyExprsAs_structExprs childSource) children).bind fun values =>
      StorageWalkAction.emitDef _ stack loop (.arrLit type values) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_structLiteral {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (type : Ty) (exprs : List Expr)
    (children : ∀ expr ∈ exprs, StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceExpression env results stack (.structLit type exprs) := by
  intro result start finish source visible loop
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ := tyExpr_structLiteral_children source
  exact ((storageWalk_source_expressions exprs visible loop childSource children).bind fun values =>
    StorageWalkAction.emitDef _ stack loop (.structLit type values) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_fill {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (type : Ty) (expr : Expr)
    (child : StorageWalkSourceExpression env results stack expr) : StorageWalkSourceExpression env results stack (.fill type expr) := by
  intro result start finish source visible loop
  obtain ⟨_, element, count, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  exact ((child childSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.arrFill type value) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_pop {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (owner : Place) (origin : OriginId)
    (child : StorageWalkSourcePlace env results stack owner) : StorageWalkSourceExpression env results stack (.pop owner origin) := by
  intro result start finish source visible loop
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  exact ((child ownerSource visible loop).bind fun value =>
    StorageWalkAction.emitDef _ stack loop (.pop value (some origin)) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_push {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (owner : Place) (expr : Expr) (origin : Option OriginId)
    (placeChild : StorageWalkSourcePlace env results stack owner) (exprChild : StorageWalkSourceExpression env results stack expr) :
    StorageWalkSourceExpression env results stack (.push owner expr origin) := by
  intro result start finish source visible loop
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerSource, shape, childSource, _⟩ :=
    tyExpr_push_children source
  exact ((placeChild ownerSource visible loop).bind fun ownerValue =>
    (exprChild childSource visible loop).bind fun value =>
      StorageWalkAction.emitDef _ stack loop (.push ownerValue value origin) (by simp [StorageInstructionVisible]))

theorem storageWalk_source_arguments {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (args : List Arg)
    (visible : StorageWalkVisible env stack) (loop : Option LoopCtx)
    {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    (children : ∀ arg ∈ args, StorageWalkSourceArgument env results stack arg) :
    StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerArgs args) := by
  induction args generalizing params start with
  | nil => exact (StorageWalkAction.pure _ stack loop [])
  | cons arg args inductionHypothesis =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      have restLength : params.length = args.length := by simpa using sameLength
      cases arg with
      | byVal expr =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
          tyArgs_byVal_head source
        have child : StorageWalkSourceExpression env results stack expr := children (.byVal expr) (by simp)
        exact ((child childSource visible loop).bind fun value =>
          (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member]))).bind fun values =>
              StorageWalkAction.pure _ stack loop (value :: values))
      | byRef mu place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
          tyArgs_byRef_head source
        have child : StorageWalkSourcePlace env results stack place := children (.byRef mu place) (by simp)
        have argument : StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerArg (.byRef mu place)) :=
          (child placeSource visible loop).bind fun value => StorageWalkAction.borrowTo _ stack loop mu value
        exact (argument.bind fun value =>
          (inductionHypothesis restLength restSource
            (fun arg member => children arg (by simp [member]))).bind fun values =>
              StorageWalkAction.pure _ stack loop (value :: values))

theorem storageWalk_source_call {env : Core.TEnv} {results : List Ty} {stack : List ScopeId} (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, StorageWalkSourceArgument env results stack arg) :
    StorageWalkSourceExpression env results stack (.call context args origin) := by
  intro type start finish source visible loop
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt, length, argsSource, resultSource⟩ :=
    tyExpr_call_tables source
  refine (storageWalk_source_arguments args visible loop length argsSource children).bind fun values =>
    (StorageWalkAction.emitDef _ stack loop (.call context values (some origin)) (by simp [StorageInstructionVisible])).bind fun value =>
      (StorageWalkAction.read _ stack loop).bind fun reader => ?_
  cases reader.mod.noReturn context
  · exact StorageWalkAction.pure _ stack loop value
  · exact (StorageWalkAction.emitTerm _ stack loop .unreachable rfl
      (by intro entry target member; cases member) (by intro state target member; cases member)).bind fun _ => StorageWalkAction.pure _ stack loop value

#print axioms storageWalk_source_bound_omitted
#print axioms storageWalk_source_bound_expr
#print axioms storageWalk_source_bound_fromEnd
#print axioms storageWalk_source_slice
#print axioms storageWalk_source_expressions
#print axioms storageWalk_source_arrayLiteral
#print axioms storageWalk_source_structLiteral
#print axioms storageWalk_source_fill
#print axioms storageWalk_source_pop
#print axioms storageWalk_source_push
#print axioms storageWalk_source_arguments
#print axioms storageWalk_source_call

end Goose.Lower.Validation
