import Goose.Proofs.ExitExecutionEvaluationStatementLet

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem execStmt_assign_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.assign p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_assignOp_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (op : Goose.Core.BinOp) (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.assignOp op p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_rebind_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.rebind x e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_expr_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.expr e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_append_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (v : View) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.append p v org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_popN_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.popN p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_resize_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (fill : Option Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.resize p e fill org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_clear_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.clear p org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_assignWhole_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.assignWhole p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_ifS_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (c : Expr) (a : Block) (b : Option Block) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.ifS c a b org)) := by
  cases b <;> simp only [execStmt]
  all_goals fresh_eval previous

theorem execStmt_while_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (c : Expr) (b : Block) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.while c b org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_forRange_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (lo hi : Expr) (b : Block) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.forRange x lo hi b org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_forEach_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (index : Option Goose.Core.VarId) (v : View) (byRef : Bool) (b : Block) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.forEach x index v byRef b org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_receive_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (vars : List Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.receive vars e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_appendValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.appendValue p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_appendConstruct_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.appendConstruct p e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_retValues_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (es : List Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.retValues es org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_retForward_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.retForward e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_returnFrom_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (target : Nat) (es : List Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.returnFrom target es org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_returnFromForward_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (target : Nat) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.returnFromForward target e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_breakValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.breakValue e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_ret_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Option Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.ret e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_brk_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.brk org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_cont_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.cont org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_print_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (args : List PrintArg) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.print args org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_assertS_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.assertS e org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_abort_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (msg : String) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.abort msg org)) := by
  simp only [execStmt]
  fresh_eval previous

theorem execStmt_exit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesFresh (execStmt (fuel + 1) config environment (.exit e org)) := by
  simp only [execStmt]
  fresh_eval previous

end Goose.Proofs.ExitExecution
