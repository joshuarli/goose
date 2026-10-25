import Goose.Lower.DemandExpressionResult
import Goose.Evidence.Execution

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive ExpressionLeafDemand {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) (map : RetainedSsaMap) (cx : FnCtx)
    (before built : LS) (initial : GIR.Frame) (start : Pt) (id : ValueId) :
    DemandRuntimePoint → Prop
  | entry
      (valid : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs ⟨start, initial, state⟩) :
      ExpressionLeafDemand source map cx before built initial start id ⟨start, initial, state⟩
  | exit {value : Val} {after : St}
      (boundary : ExpressionDemandBoundary source map cx before initial built id value after
        (start.1, start.2 + 1) (initial.set id (.val value))) :
      ExpressionLeafDemand source map cx before built initial start id
        ⟨(start.1, start.2 + 1), initial.set id (.val value), after⟩

theorem accepted_expression_leaf_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr}
    {state after : St} (source : ExprSource cfg env expression state)
    {sourceFuel : Nat} {value : Val}
    (done : evalExpr sourceFuel cfg env expression state = .ok value after)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {op : Op}
    {le : LEnv} (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef op le before = (id, built)) (point : before.pp = some start)
    (extension : ExtT built cx.fn.blocks) (related : Rel cfg env cx initial before)
    (notCall : ∀ context arguments origin, op ≠ .call context arguments origin)
    (operation : execPure cx initial op state = .ok (.val value) after) :
    DemandUniformTraversal cx (ExpressionLeafDemand source map cx before built initial start id) 1
      ⟨start, initial, state⟩ ⟨(start.1, start.2 + 1), initial.set id (.val value), after⟩ := by
  obtain ⟨post, instruction⟩ := Post.def_leaf (Post.init related point) emitted extension (.val value)
  have boundary := ExpressionDemandBoundary.of_result (source.result sourceFuel value done)
    admitted bounded realized post
  refine .next (.entry ⟨⟨before, point, related⟩, source.frame, realized⟩) ?_ (.done (.exit boundary))
  intro fuel
  apply DemandInstructionStep.definition instruction
  have pureOp : execOp fuel cx initial op = execPure cx initial op := by
    cases op with
    | call context arguments origin => exact (notCall context arguments origin rfl).elim
    | _ => unfold execOp; rfl
  rw [pureOp]
  exact operation

theorem accepted_literal_demand_traversal {cfg : Cfg} {env : Env} {state : St}
    {type : IntTy} {number : Int} (source : ExprSource cfg env (.lit type number) state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr (.lit type number) le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before) :
    DemandUniformTraversal cx (ExpressionLeafDemand source map cx before built initial start id) 1
      ⟨start, initial, state⟩ ⟨(start.1, start.2 + 1), initial.set id (.val (.int type number)), state⟩ := by
  have emitted : emitDef (.constInt type number) le before = (id, built) := by
    simpa only [lowerExpr] using lowered
  exact accepted_expression_leaf_demand_traversal source (sourceFuel := 1) (by simp only [evalExpr, pure_apply]) admitted bounded
    realized emitted point extension related (by intro context arguments origin impossible; cases impossible) rfl

theorem accepted_boolean_demand_traversal {cfg : Cfg} {env : Env} {state : St}
    {boolean : Bool} (source : ExprSource cfg env (.bool boolean) state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr (.bool boolean) le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before) :
    DemandUniformTraversal cx (ExpressionLeafDemand source map cx before built initial start id) 1
      ⟨start, initial, state⟩ ⟨(start.1, start.2 + 1), initial.set id (.val (.bool boolean)), state⟩ := by
  have emitted : emitDef (.constBool boolean) le before = (id, built) := by
    simpa only [lowerExpr] using lowered
  exact accepted_expression_leaf_demand_traversal source (sourceFuel := 1) (by simp only [evalExpr, pure_apply]) admitted bounded
    realized emitted point extension related (by intro context arguments origin impossible; cases impossible) rfl

end Goose.Lower
