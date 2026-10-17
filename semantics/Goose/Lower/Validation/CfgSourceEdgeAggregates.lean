import Goose.Lower.Validation.CfgSourceEdgeContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_emptyExpressions (env : Core.TEnv) (results : List Ty) : CfgSourceExpressions env results [] := by
  intro types start finish source
  exact generated_edge_pure _ _ _

theorem cfg_source_consExpressions {env : Core.TEnv} {results : List Ty} (expr : Expr) (rest : List Expr)
    (child : CfgSourceExpression env results expr) (restChild : CfgSourceExpressions env results rest) :
    CfgSourceExpressions env results (expr :: rest) := by
  intro types start finish source
  cases types with
  | nil => exact (rej_ok _ _ _ _).mp source |>.elim
  | cons ty types =>
    simp only [Core.tyStructExprs] at source
    obtain ⟨childTy, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases same : (childTy == ty) = true
    · simp only [same, ite_true] at source
      exact (child childSource).bind fun _ => (restChild source).bind fun _ => generated_edge_pure _ _ _
    · simp [same, chk] at source

theorem cfg_source_arrayLiteral {env : Core.TEnv} {results : List Ty} (ty : Ty) (exprs : List Expr)
    (children : CfgSourceExpressions env results exprs) : CfgSourceExpression env results (.arrLit ty exprs) := by
  intro output start finish source
  obtain ⟨_, element, childStart, childFinish, _, _, childSource⟩ := tyExpr_arrayLiteral_children source
  exact (children (tyExprsAs_structExprs childSource)).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_structLiteral {env : Core.TEnv} {results : List Ty} (ty : Ty) (exprs : List Expr)
    (children : CfgSourceExpressions env results exprs) : CfgSourceExpression env results (.structLit ty exprs) := by
  intro output start finish source
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, _, childSource⟩ := tyExpr_structLiteral_children source
  exact (children childSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_fill {env : Core.TEnv} {results : List Ty} (ty : Ty) (expr : Expr)
    (child : CfgSourceExpression env results expr) : CfgSourceExpression env results (.fill ty expr) := by
  intro output start finish source
  obtain ⟨_, element, size, childStart, childFinish, _, childSource⟩ := tyExpr_fill_child source
  exact (child childSource).bind fun _ => generated_edge_emitDef _ _ _

theorem cfg_source_emptyArguments (env : Core.TEnv) (results : List Ty) : CfgSourceArguments env results [] := by
  intro callee params start finish length source
  exact generated_edge_pure _ _ _

theorem cfg_source_valueArgument {env : Core.TEnv} {results : List Ty} (expr : Expr) (rest : List Arg)
    (child : CfgSourceExpression env results expr) (restChild : CfgSourceArguments env results rest) :
    CfgSourceArguments env results (.byVal expr :: rest) := by
  intro callee params start finish length source
  cases params with
  | nil => simp at length
  | cons param params =>
    obtain ⟨localVar, childTy, childStart, childFinish, restStart, _, childSource, _, restSource⟩ := tyArgs_byVal_head source
    exact (child childSource).bind fun _ => (restChild (by simpa using length) restSource).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_referenceArgument {env : Core.TEnv} {results : List Ty} (mu : Mutability) (place : Place) (rest : List Arg)
    (child : CfgSourcePlace env results place) (restChild : CfgSourceArguments env results rest) :
    CfgSourceArguments env results (.byRef mu place :: rest) := by
  intro callee params start finish length source
  cases params with
  | nil => simp at length
  | cons param params =>
    obtain ⟨localVar, info, childFinish, restStart, _, childSource, _, _, restSource⟩ := tyArgs_byRef_head source
    exact ((child childSource).bind fun value => generated_edge_borrowTo _ _ mu value).bind fun _ =>
      (restChild (by simpa using length) restSource).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_call {env : Core.TEnv} {results : List Ty} (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : CfgSourceArguments env results args) : CfgSourceExpression env results (.call context args origin) := by
  intro output start finish source
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, _, _, length, argsSource, _⟩ := tyExpr_call_tables source
  refine (children length argsSource).bind fun values => ?_
  refine (generated_edge_emitDef _ _ _).bind fun value => ?_
  refine (generated_edge_read _ _).bind fun reader => ?_
  by_cases stopping : reader.mod.noReturn context = true
  · simp only [stopping, ite_true]
    exact (generated_edge_emitTerm _ _ .unreachable (fun _ => trivial)).bind fun _ => generated_edge_pure _ _ value
  · simp only [stopping]
    exact generated_edge_pure _ _ value

end Goose.Lower.Validation
