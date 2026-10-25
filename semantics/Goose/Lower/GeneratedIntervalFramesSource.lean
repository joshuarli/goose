import Goose.Lower.GeneratedIntervalFramesBuilder

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem generatedIntervalFrame_lowerExpr (loop : Option LoopCtx) (deferred : List BlockId) (expr : Expr) :
    GeneratedIntervalFrameRun loop deferred (lowerExpr expr) :=
  .of_frames (generatedTargetFrame_lowerExpr loop expr) deferred

theorem generatedIntervalFrame_lowerExprs (loop : Option LoopCtx) (deferred : List BlockId) (exprs : List Expr) :
    GeneratedIntervalFrameRun loop deferred (lowerExprs exprs) :=
  .of_frames (generatedTargetFrame_lowerExprs loop exprs) deferred

theorem generatedIntervalFrame_lowerArg (loop : Option LoopCtx) (deferred : List BlockId) (arg : Arg) :
    GeneratedIntervalFrameRun loop deferred (lowerArg arg) :=
  .of_frames (generatedTargetFrame_lowerArg loop arg) deferred

theorem generatedIntervalFrame_lowerArgs (loop : Option LoopCtx) (deferred : List BlockId) (args : List Arg) :
    GeneratedIntervalFrameRun loop deferred (lowerArgs args) :=
  .of_frames (generatedTargetFrame_lowerArgs loop args) deferred

theorem generatedIntervalFrame_lowerPlace (loop : Option LoopCtx) (deferred : List BlockId) (place : Place) :
    GeneratedIntervalFrameRun loop deferred (lowerPlace place) :=
  .of_frames (generatedTargetFrame_lowerPlace loop place) deferred

theorem generatedIntervalFrame_lowerView (loop : Option LoopCtx) (deferred : List BlockId) (view : View) :
    GeneratedIntervalFrameRun loop deferred (lowerView view) :=
  .of_frames (generatedTargetFrame_lowerView loop view) deferred

theorem generatedIntervalFrame_lowerBound (loop : Option LoopCtx) (deferred : List BlockId) (bound : Bound) :
    GeneratedIntervalFrameRun loop deferred (lowerBound bound) :=
  .of_frames (generatedTargetFrame_lowerBound loop bound) deferred

theorem generatedIntervalFrame_lowerEachSource (loop : Option LoopCtx) (deferred : List BlockId) (view : View) :
    GeneratedIntervalFrameRun loop deferred (lowerEachSource view) :=
  .of_frames (generatedTargetFrame_lowerEachSource loop view) deferred

theorem generatedIntervalFrame_lowerBlockValue (loop : Option LoopCtx) (deferred : List BlockId) (want : Bool) (value : Option Expr) :
    GeneratedIntervalFrameRun loop deferred (lowerBlockValue want value) :=
  .of_frames (generatedTargetFrame_lowerBlockValue loop want value) deferred

theorem generatedIntervalFrame_lowerBlock (loop : Option LoopCtx) (deferred : List BlockId)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (body : Core.Block) :
    GeneratedIntervalFrameRun loop deferred (lowerBlock loop pre want body) :=
  .of_frames (generatedTargetFrame_lowerBlock loop pre want body) deferred

theorem generatedIntervalFrame_lowerStmts (loop : Option LoopCtx) (deferred : List BlockId) (stmts : List Stmt) :
    GeneratedIntervalFrameRun loop deferred (lowerStmts loop stmts) :=
  .of_frames (generatedTargetFrame_lowerStmts loop stmts) deferred

theorem generatedIntervalFrame_lowerPrintArgs (loop : Option LoopCtx) (deferred : List BlockId) (args : List PrintArg) :
    GeneratedIntervalFrameRun loop deferred (lowerPrintArgs args) :=
  .of_frames (generatedTargetFrame_lowerPrintArgs loop args) deferred

theorem generatedIntervalFrame_lowerStmt (loop : Option LoopCtx) (deferred : List BlockId) (stmt : Stmt) :
    GeneratedIntervalFrameRun loop deferred (lowerStmt loop stmt) :=
  .of_frames (generatedTargetFrame_lowerStmt loop stmt) deferred

end Goose.Lower
