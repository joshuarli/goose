import Goose.Lower.Validation.CfgSourceEdgeContracts
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_emptyPrintArguments (env : Core.TEnv) (results : List Ty) : CfgSourcePrintArguments env results [] := by
  intro start finish source
  exact generated_edge_pure _ _ _

theorem cfg_source_textPrintArgument {env : Core.TEnv} {results : List Ty} (text : String) (rest : List PrintArg)
    (child : CfgSourcePrintArguments env results rest) : CfgSourcePrintArguments env results (.text text :: rest) := by
  intro start finish source
  exact (child source).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_expressionPrintArgument {env : Core.TEnv} {results : List Ty} (expr : Expr) (rest : List PrintArg)
    (child : CfgSourceExpression env results expr) (restChild : CfgSourcePrintArguments env results rest) :
    CfgSourcePrintArguments env results (.expr expr :: rest) := by
  intro start finish source
  obtain ⟨ty, childFinish, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
  cases ty <;> try exact (rej_ok _ _ _ _).mp tail |>.elim
  all_goals exact (child childSource).bind fun _ => (restChild tail).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_expressionStatement {env : Core.TEnv} {results : List Ty} (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.expr expr origin) := by
  intro output scope start finish source context
  obtain ⟨ty, childSource, _⟩ := tyStmt_expr_children source
  exact ((child childSource).withLoop context).bind fun _ => generated_edge_pure _ _ _

theorem cfg_source_print {env : Core.TEnv} {results : List Ty} (args : List PrintArg) (origin : OriginId)
    (child : CfgSourcePrintArguments env results args) : CfgSourceStatement env results (.print args origin) := by
  intro output scope start finish source context
  have childSource := (tyStmt_print_children source).1
  exact ((child childSource).withLoop context).bind fun _ => generated_edge_emitEffect _ _ _

theorem cfg_source_assert {env : Core.TEnv} {results : List Ty} (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.assertS expr origin) := by
  intro output scope start finish source context
  have childSource := (tyStmt_assert_children source).1
  exact ((child childSource).withLoop context).bind fun condition => generated_edge_assert_core _ _ condition origin

theorem cfg_source_abort (env : Core.TEnv) (results : List Ty) (kind : String) (origin : OriginId) :
    CfgSourceStatement env results (.abort kind origin) := by
  intro output scope start finish source context
  exact generated_edge_emitTerm _ _ _ (fun _ => trivial)

theorem cfg_source_exit {env : Core.TEnv} {results : List Ty} (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.exit expr origin) := by
  intro output scope start finish source context
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact ((child childSource).withLoop context).bind fun _ => generated_edge_emitTerm _ _ _ (fun _ => trivial)

theorem cfg_source_returnUnit (env : Core.TEnv) (results : List Ty) (origin : OriginId) :
    CfgSourceStatement env results (.ret none origin) := by
  intro output scope start finish source context
  exact (generated_edge_pure _ _ _).bind fun _ => (generated_edge_leaveTo _ _ 0).bind fun _ =>
    generated_edge_emitTerm _ _ _ (fun _ => trivial)

theorem cfg_source_returnValue {env : Core.TEnv} {results : List Ty} (expr : Expr) (origin : OriginId)
    (child : CfgSourceExpression env results expr) : CfgSourceStatement env results (.ret (some expr) origin) := by
  intro output scope start finish source context
  obtain ⟨expected, actual, impl, _, _, _, childSource, _⟩ := tyStmt_return_children source
  exact (((child childSource).withLoop context).bind fun value => (generated_edge_coerceResult _ _ value origin).bind fun converted =>
    generated_edge_pure _ _ [converted]).bind fun values => (generated_edge_leaveTo _ _ 0).bind fun _ =>
      generated_edge_emitTerm _ _ (.ret values (some origin)) (fun _ => trivial)

theorem cfg_source_break (env : Core.TEnv) (results : List Ty) (origin : OriginId) :
    CfgSourceStatement env results (.brk origin) := by
  intro output scope start finish source context
  exact generated_edge_lowerBreak _ _ _

theorem cfg_source_continue (env : Core.TEnv) (results : List Ty) (origin : OriginId) :
    CfgSourceStatement env results (.cont origin) := by
  intro output scope start finish source context
  exact generated_edge_lowerContinue _ _ _

end Goose.Lower.Validation
