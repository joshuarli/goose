import Goose.Lower.DemandExpressionSuffix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem bin_demand_traversal {cfg : Cfg} {env : Env} {a b : Expr} {state afterLeft afterRight : St}
    {operation : BinOp} {origin : OriginId} (source : ExprSource cfg env (.bin operation a b origin) state)
    (left : ExprSource cfg env a state) (right : ExprSource cfg env b afterLeft)
    (leftMetadata : source.ChildAt left 0 rfl) (rightMetadata : source.ChildAt right 1 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before first second built : LS} {initial middleFrame frame : GIR.Frame}
    {start middlePoint point : Pt} {leftId rightId id : ValueId} {le : LEnv}
    {leftFuel rightFuel : Nat} {type : IntTy} {leftNumber rightNumber result : Int}
    (leftDone : evalExpr leftFuel cfg env a state = .ok (.int type leftNumber) afterLeft)
    (rightDone : evalExpr rightFuel cfg env b afterLeft = .ok (.int type rightNumber) afterRight)
    (computed : evalBin cfg.profile operation type leftNumber rightNumber = .ok result)
    (leftPost : Post cfg env cx before initial first middleFrame middlePoint [(leftId, .val (.int type leftNumber))])
    (rightPost : Post cfg env cx first middleFrame second frame point [(rightId, .val (.int type rightNumber))])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef (.bin operation type leftId rightId (some origin)) le second = (id, built))
    (extension : ExtT built cx.fn.blocks) {leftLength rightLength fuel : Nat}
    (room : leftLength + rightLength < fuel)
    (leftTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx left) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩)
    (rightTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx right) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩) :
    evalExpr (max leftFuel rightFuel + 1) cfg env (.bin operation a b origin) state =
        .ok (.int type result) afterRight ∧
      ExpressionDemandBoundary source map cx before initial built id (.int type result) afterRight
        (point.1, point.2 + 1) (frame.set id (.val (.int type result))) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (leftLength + rightLength + 1) fuel
        ⟨start, initial, state⟩ ⟨(point.1, point.2 + 1), frame.set id (.val (.int type result)), afterRight⟩ := by
  have leftDone' := (((monoAll leftFuel (max leftFuel rightFuel) (Nat.le_max_left _ _)).expr cfg env a) state).1
    (.int type leftNumber) afterLeft leftDone
  have rightDone' := (((monoAll rightFuel (max leftFuel rightFuel) (Nat.le_max_right _ _)).expr cfg env b) afterLeft).1
    (.int type rightNumber) afterRight rightDone
  have sourceDone : evalExpr (max leftFuel rightFuel + 1) cfg env (.bin operation a b origin) state =
      .ok (.int type result) afterRight := by
    simp only [evalExpr, bind_apply, leftDone', rightDone', Core.expectInt, Core.expectSameTy,
      ite_true, pure_apply, computed]
  have post := leftPost.comp rightPost
  have leftCell := post.has (leftId, .val (.int type leftNumber)) (by simp)
  have rightCell := post.has (rightId, .val (.int type rightNumber)) (by simp)
  have execution : execPure cx frame (.bin operation type leftId rightId (some origin)) afterRight =
      .ok (.val (.int type result)) afterRight := by
    rw [execPure_bin rightPost.rel.prof leftCell rightCell, computed]
    rfl
  have first : DemandTraversal cx (CanonicalExpressionDemand map cx source) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩ :=
    leftTraversal.mono (fun _ demanded => .child leftMetadata demanded)
  have second : DemandTraversal cx (CanonicalExpressionDemand map cx source) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩ :=
    rightTraversal.mono (fun _ demanded => .child rightMetadata demanded)
  obtain ⟨boundary, steps⟩ := expression_definition_demand_traversal source sourceDone admitted post bounded realized
    emitted extension (by intro context arguments origin impossible; cases impossible) execution room (first.append second)
  exact ⟨sourceDone, boundary, steps⟩

theorem bin_demand_abort {cfg : Cfg} {env : Env} {a b : Expr} {state afterLeft afterRight : St}
    {operation : BinOp} {origin : OriginId} (source : ExprSource cfg env (.bin operation a b origin) state)
    (left : ExprSource cfg env a state) (right : ExprSource cfg env b afterLeft)
    (leftMetadata : source.ChildAt left 0 rfl) (rightMetadata : source.ChildAt right 1 rfl)
    {map : RetainedSsaMap} {cx : FnCtx} {before first second built : LS} {initial middleFrame frame : GIR.Frame}
    {start middlePoint point : Pt} {leftId rightId id : ValueId} {le : LEnv}
    {leftFuel rightFuel : Nat} {type : IntTy} {leftNumber rightNumber : Int} {kind : NumAbort}
    (leftDone : evalExpr leftFuel cfg env a state = .ok (.int type leftNumber) afterLeft)
    (rightDone : evalExpr rightFuel cfg env b afterLeft = .ok (.int type rightNumber) afterRight)
    (computed : evalBin cfg.profile operation type leftNumber rightNumber = .error kind)
    (leftPost : Post cfg env cx before initial first middleFrame middlePoint [(leftId, .val (.int type leftNumber))])
    (rightPost : Post cfg env cx first middleFrame second frame point [(rightId, .val (.int type rightNumber))])
    (emitted : emitDef (.bin operation type leftId rightId (some origin)) le second = (id, built))
    (extension : ExtT built cx.fn.blocks) {leftLength rightLength fuel : Nat}
    (room : leftLength + rightLength < fuel)
    (leftTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx left) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩)
    (rightTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx right) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩) :
    evalExpr (max leftFuel rightFuel + 1) cfg env (.bin operation a b origin) state =
        .stop (.abort (AbortKind.ofNum kind) origin) afterRight ∧
      DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) (leftLength + rightLength) fuel
        ⟨start, initial, state⟩ (.abort (AbortKind.ofNum kind) origin) afterRight := by
  have leftDone' := (((monoAll leftFuel (max leftFuel rightFuel) (Nat.le_max_left _ _)).expr cfg env a) state).1
    (.int type leftNumber) afterLeft leftDone
  have rightDone' := (((monoAll rightFuel (max leftFuel rightFuel) (Nat.le_max_right _ _)).expr cfg env b) afterLeft).1
    (.int type rightNumber) afterRight rightDone
  have sourceDone : evalExpr (max leftFuel rightFuel + 1) cfg env (.bin operation a b origin) state =
      .stop (.abort (AbortKind.ofNum kind) origin) afterRight := by
    simp only [evalExpr, bind_apply, leftDone', rightDone', Core.expectInt, Core.expectSameTy,
      ite_true, pure_apply, computed, abortAt, M.stop]
  have post := leftPost.comp rightPost
  have leftCell := post.has (leftId, .val (.int type leftNumber)) (by simp)
  have rightCell := post.has (rightId, .val (.int type rightNumber)) (by simp)
  have execution : execPure cx frame (.bin operation type leftId rightId (some origin)) afterRight =
      .stop (.abort (AbortKind.ofNum kind) origin) afterRight := by
    rw [execPure_bin rightPost.rel.prof leftCell rightCell, computed]
    rfl
  have first : DemandTraversal cx (CanonicalExpressionDemand map cx source) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩ :=
    leftTraversal.mono (fun _ demanded => .child leftMetadata demanded)
  have second : DemandTraversal cx (CanonicalExpressionDemand map cx source) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩ :=
    rightTraversal.mono (fun _ demanded => .child rightMetadata demanded)
  refine ⟨sourceDone, expression_definition_demand_stopped source post emitted extension
    (by intro context arguments origin impossible; cases impossible) execution room (first.append second)⟩

theorem cmp_demand_traversal {cfg : Cfg} {env : Env} {a b : Expr} {state afterLeft afterRight : St}
    {operation : CmpOp} (source : ExprSource cfg env (.cmp operation a b) state)
    (left : ExprSource cfg env a state) (right : ExprSource cfg env b afterLeft)
    (leftMetadata : source.ChildAt left 0 rfl) (rightMetadata : source.ChildAt right 1 rfl)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before first second built : LS} {initial middleFrame frame : GIR.Frame}
    {start middlePoint point : Pt} {leftId rightId id : ValueId} {le : LEnv}
    {leftFuel rightFuel : Nat} {leftValue rightValue : Val} {leftNumber rightNumber : Int} {instruction : Op}
    (leftDone : evalExpr leftFuel cfg env a state = .ok leftValue afterLeft)
    (rightDone : evalExpr rightFuel cfg env b afterLeft = .ok rightValue afterRight)
    (compared : expectComparable leftValue rightValue = pure (leftNumber, rightNumber))
    (leftPost : Post cfg env cx before initial first middleFrame middlePoint [(leftId, .val leftValue)])
    (rightPost : Post cfg env cx first middleFrame second frame point [(rightId, .val rightValue)])
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (emitted : emitDef instruction le second = (id, built))
    (kind : instruction = .boolCmp operation leftId rightId ∨ ∃ type, instruction = .cmp operation type leftId rightId)
    (extension : ExtT built cx.fn.blocks) {leftLength rightLength fuel : Nat}
    (room : leftLength + rightLength < fuel)
    (leftTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx left) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩)
    (rightTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx right) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩) :
    evalExpr (max leftFuel rightFuel + 1) cfg env (.cmp operation a b) state =
        .ok (.bool (evalCmp operation leftNumber rightNumber)) afterRight ∧
      ExpressionDemandBoundary source map cx before initial built id (.bool (evalCmp operation leftNumber rightNumber))
        afterRight (point.1, point.2 + 1) (frame.set id (.val (.bool (evalCmp operation leftNumber rightNumber)))) ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (leftLength + rightLength + 1) fuel
        ⟨start, initial, state⟩
        ⟨(point.1, point.2 + 1), frame.set id (.val (.bool (evalCmp operation leftNumber rightNumber))), afterRight⟩ := by
  have leftDone' := (((monoAll leftFuel (max leftFuel rightFuel) (Nat.le_max_left _ _)).expr cfg env a) state).1
    leftValue afterLeft leftDone
  have rightDone' := (((monoAll rightFuel (max leftFuel rightFuel) (Nat.le_max_right _ _)).expr cfg env b) afterLeft).1
    rightValue afterRight rightDone
  have sourceDone : evalExpr (max leftFuel rightFuel + 1) cfg env (.cmp operation a b) state =
      .ok (.bool (evalCmp operation leftNumber rightNumber)) afterRight := by
    simp only [evalExpr, bind_apply, leftDone', rightDone', compared, pure_apply]
  have post := leftPost.comp rightPost
  have leftCell := post.has (leftId, .val leftValue) (by simp)
  have rightCell := post.has (rightId, .val rightValue) (by simp)
  have execution : execPure cx frame instruction afterRight =
      .ok (.val (.bool (evalCmp operation leftNumber rightNumber))) afterRight := by
    rcases kind with rfl | ⟨type, rfl⟩
    · rw [(execPure_cmp leftCell rightCell).2, compared]
      rfl
    · rw [(execPure_cmp leftCell rightCell).1 type, compared]
      rfl
  have first : DemandTraversal cx (CanonicalExpressionDemand map cx source) leftLength fuel
      ⟨start, initial, state⟩ ⟨middlePoint, middleFrame, afterLeft⟩ :=
    leftTraversal.mono (fun _ demanded => .child leftMetadata demanded)
  have second : DemandTraversal cx (CanonicalExpressionDemand map cx source) rightLength (fuel - leftLength)
      ⟨middlePoint, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩ :=
    rightTraversal.mono (fun _ demanded => .child rightMetadata demanded)
  have notCall : ∀ context arguments origin, instruction ≠ .call context arguments origin := by
    rcases kind with rfl | ⟨type, rfl⟩ <;> intro context arguments origin impossible <;> cases impossible
  obtain ⟨boundary, steps⟩ := expression_definition_demand_traversal source sourceDone admitted post bounded realized
    emitted extension notCall execution room (first.append second)
  exact ⟨sourceDone, boundary, steps⟩

end Goose.Lower
