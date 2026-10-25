import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesProducers

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem execStmt_letS_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.letS x e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_assign_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.assign p e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_assignOp_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (op : Goose.Core.BinOp) (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.assignOp op p e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_rebind_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.rebind x e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_expr_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.expr e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_append_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (src : View) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.append owner src org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_popN_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (count : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.popN owner count org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_resize_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (size : Expr) (fill : Option Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.resize owner size fill org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_clear_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.clear owner org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_assignWhole_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (replacement : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.assignWhole owner replacement org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_ifS_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (c : Expr) (thenB : Block) (elseB : Option Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.ifS c thenB elseB org)) := by
  cases elseB <;> simp only [execStmt]
  all_goals evaluation_frame previous

private theorem execStmt_while_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (c : Expr) (body : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.while c body org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_forRange_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (x : Goose.Core.VarId) (lo hi : Expr) (body : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.forRange x lo hi body org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_forEach_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (x : Goose.Core.VarId) (index : Option Goose.Core.VarId) (v : View) (byRef : Bool) (body : Block) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.forEach x index v byRef body org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_receive_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (vars : List Goose.Core.VarId) (producer : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.receive vars producer org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_appendValue_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (producer : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.appendValue owner producer org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_appendConstruct_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (owner : Place) (producer : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.appendConstruct owner producer org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_retValues_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (operands : List Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.retValues operands org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_retForward_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (call : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.retForward call org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_returnFrom_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (target : Nat) (operands : List Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.returnFrom target operands org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_returnFromForward_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (target : Nat) (call : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.returnFromForward target call org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_breakValue_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (value : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.breakValue value org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_ret_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (e : Option Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.ret e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_brk_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.brk org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_cont_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.cont org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_print_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (args : List PrintArg) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.print args org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_assertS_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.assertS e org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_abort_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (message : String) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.abort message org)) := by
  simp only [execStmt]
  evaluation_frame previous

private theorem execStmt_exit_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (e : Expr) (org : Goose.Core.OriginId) :
    BreakFrameAction (execStmt (fuel + 1) config environment (Stmt.exit e org)) := by
  simp only [execStmt]
  evaluation_frame previous

theorem execStmt_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
     (input : Stmt) :
    BreakFrameAction (execStmt (fuel + 1) config environment input) := by
  cases input with
  | letS x e org => exact execStmt_letS_breakFrame_succ fuel config previous environment x e org
  | assign p e org => exact execStmt_assign_breakFrame_succ fuel config previous environment p e org
  | assignOp op p e org => exact execStmt_assignOp_breakFrame_succ fuel config previous environment op p e org
  | rebind x e org => exact execStmt_rebind_breakFrame_succ fuel config previous environment x e org
  | expr e org => exact execStmt_expr_breakFrame_succ fuel config previous environment e org
  | append owner src org => exact execStmt_append_breakFrame_succ fuel config previous environment owner src org
  | popN owner count org => exact execStmt_popN_breakFrame_succ fuel config previous environment owner count org
  | resize owner size fill org => exact execStmt_resize_breakFrame_succ fuel config previous environment owner size fill org
  | clear owner org => exact execStmt_clear_breakFrame_succ fuel config previous environment owner org
  | assignWhole owner replacement org => exact execStmt_assignWhole_breakFrame_succ fuel config previous environment owner replacement org
  | ifS c thenB elseB org => exact execStmt_ifS_breakFrame_succ fuel config previous environment c thenB elseB org
  | «while» c body org => exact execStmt_while_breakFrame_succ fuel config previous environment c body org
  | forRange x lo hi body org => exact execStmt_forRange_breakFrame_succ fuel config previous environment x lo hi body org
  | forEach x index v byRef body org => exact execStmt_forEach_breakFrame_succ fuel config previous environment x index v byRef body org
  | receive vars producer org => exact execStmt_receive_breakFrame_succ fuel config previous environment vars producer org
  | appendValue owner producer org => exact execStmt_appendValue_breakFrame_succ fuel config previous environment owner producer org
  | appendConstruct owner producer org => exact execStmt_appendConstruct_breakFrame_succ fuel config previous environment owner producer org
  | retValues operands org => exact execStmt_retValues_breakFrame_succ fuel config previous environment operands org
  | retForward call org => exact execStmt_retForward_breakFrame_succ fuel config previous environment call org
  | returnFrom target operands org => exact execStmt_returnFrom_breakFrame_succ fuel config previous environment target operands org
  | returnFromForward target call org => exact execStmt_returnFromForward_breakFrame_succ fuel config previous environment target call org
  | breakValue value org => exact execStmt_breakValue_breakFrame_succ fuel config previous environment value org
  | ret e org => exact execStmt_ret_breakFrame_succ fuel config previous environment e org
  | brk org => exact execStmt_brk_breakFrame_succ fuel config previous environment org
  | cont org => exact execStmt_cont_breakFrame_succ fuel config previous environment org
  | print args org => exact execStmt_print_breakFrame_succ fuel config previous environment args org
  | assertS e org => exact execStmt_assertS_breakFrame_succ fuel config previous environment e org
  | abort message org => exact execStmt_abort_breakFrame_succ fuel config previous environment message org
  | exit e org => exact execStmt_exit_breakFrame_succ fuel config previous environment e org

end Goose.Proofs.ConstructionDelivery
