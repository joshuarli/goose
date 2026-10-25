import Goose.Lower.DemandLeaves
import Goose.Lower.DemandExpressionCursor

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive BooleanNotExpression : Expr → Prop
  | boolean (value : Bool) : BooleanNotExpression (.bool value)
  | negate {expression : Expr} (child : BooleanNotExpression expression) : BooleanNotExpression (.not expression)

def BooleanNotExpression.instructions {expression : Expr} (_fragment : BooleanNotExpression expression) : Nat :=
  let rec count : Expr → Nat
    | .not child => count child + 1
    | _ => 1
  count expression

theorem accepted_boolean_expression_demand_traversal {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} (fragment : BooleanNotExpression expression) (source : ExprSource cfg env expression state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr expression le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before) :
    ∃ (sourceFuel : Nat) (value : Bool) (finalPoint : Pt) (finalFrame : GIR.Frame),
      evalExpr sourceFuel cfg env expression state = .ok (.bool value) state ∧
      Post cfg env cx before initial built finalFrame finalPoint [(id, .val (.bool value))] ∧
      DemandUniformTraversal cx (CanonicalExpressionDemand map cx source) fragment.instructions
        ⟨start, initial, state⟩ ⟨finalPoint, finalFrame, state⟩ := by
  induction fragment generalizing before built initial start id with
  | boolean value =>
    have steps := accepted_boolean_demand_traversal source admitted bounded realized lowered point extension related
    have emitted : emitDef (.constBool value) le before = (id, built) := by
      simpa only [lowerExpr] using lowered
    obtain ⟨post, _⟩ := Post.def_leaf (Post.init related point) emitted extension (.val (.bool value))
    refine ⟨1, value, (start.1, start.2 + 1), initial.set id (.val (.bool value)), (by simp only [evalExpr, pure_apply]), post, ?_⟩
    apply steps.mono
    intro runtime valid
    cases valid with
    | entry demanded => exact .entry demanded
    | exit boundary => exact .exit boundary.demanded
  | @negate expression fragment induction =>
    obtain ⟨child, typing, roots, type, metadata⟩ := source.notChild
    simp only [lowerExpr, bind_eq] at lowered
    obtain ⟨argument, middle, childLowered, emitted⟩ := lowered
    have middleExtension := extension.of_adv (adv_emitDef emitted)
    have childAdmitted : map.Admitted cfg.mod.profile child.context.retained :=
      fun shrink alias member => metadata.retained alias (admitted shrink alias member)
    have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
      simpa only [metadata.world] using realized
    obtain ⟨fuel, value, middlePoint, middleFrame, done, post, traversal⟩ :=
      induction child childAdmitted bounded childRealized childLowered point middleExtension related
    have cell := post.has (argument, .val (.bool value)) (by simp)
    have operation : execPure cx middleFrame (.boolNot argument) state =
        .ok (.val (.bool (!value))) state := by
      simp only [execPure, getVal_of cell, pure_bind, Core.expectBool, pure_apply]
    obtain ⟨finalPost, instruction⟩ := Post.def_leaf post emitted extension (.val (.bool (!value)))
    have sourceDone : evalExpr (fuel + 1) cfg env (.not expression) state = .ok (.bool (!value)) state := by
      simp only [evalExpr, bind_apply, done, Core.expectBool, pure_apply]
    have boundary := ExpressionDemandBoundary.of_result (source.result (fuel + 1) (.bool (!value)) sourceDone)
      admitted bounded realized finalPost
    have first : DemandUniformTraversal cx (CanonicalExpressionDemand map cx source) fragment.instructions
        ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, state⟩ :=
      traversal.mono (fun _ valid => .child metadata valid)
    have last : DemandUniformTraversal cx (CanonicalExpressionDemand map cx source) 1
        ⟨middlePoint, middleFrame, state⟩
        ⟨(middlePoint.1, middlePoint.2 + 1), middleFrame.set id (.val (.bool (!value))), state⟩ := by
      refine .next first.last_valid ?_ (.done (.exit boundary.demanded))
      intro residual
      exact DemandInstructionStep.definition instruction (by simpa only [execOp] using operation)
    exact ⟨fuel + 1, !value, (middlePoint.1, middlePoint.2 + 1),
      middleFrame.set id (.val (.bool (!value))), sourceDone, finalPost, first.append last⟩

theorem accepted_boolean_expression_runtime_prefix {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} (fragment : BooleanNotExpression expression) (source : ExprSource cfg env expression state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr expression le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before)
    (entry : Evidence.RuntimePoint cx.cfg cx.fn start initial state)
    {taken : Nat} {runtime : DemandRuntimePoint} (bound : taken ≤ fragment.instructions)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    Evidence.RuntimePoint cx.cfg cx.fn runtime.point runtime.frame runtime.state ∧
      CanonicalExpressionDemand map cx source runtime ∧
      map.Realizes cfg.mod source.world env runtime := by
  obtain ⟨_, _, _, _, _, _, traversal⟩ :=
    accepted_boolean_expression_demand_traversal fragment source admitted bounded realized lowered point extension related
  have cursor := traversal.runtimePrefix_invariant bound steps
  exact ⟨steps.reachable entry, cursor, cursor.carried⟩

end Goose.Lower
