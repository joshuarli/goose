import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayTrackedNativeBlock

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

private theorem initialized_stack (scope : ScopeId) (bindings : List (SlotId × ValueId × OriginId))
    (le : LEnv) (initial : LS) :
    (initSlots bindings le (Goose.Lower.pushScope scope le
      (Goose.Lower.emitEffect (.enter scope) le initial).2).2).2.stack = scope :: initial.stack := by
  rw [(advB_initSlots bindings le _ _ _ rfl).stack]
  rw [pushScope_run]
  exact congrArg (List.cons scope) (advB_emitEffect (.enter scope) le initial _ _ rfl).stack

theorem blockReplay_of_children {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {scope : ScopeId} {statements : List Stmt} {value : Option Expr} {initial : LS} {upper : Prov}
    (statementChild : ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      StatementsReplayAt nextEnv { env with scopes := scope :: env.scopes } results vt target scopeCount
        loop scope statements state provenance)
    (expressionChild : ∀ expression, value = some expression →
      SourceScopesWithin scopeCount (Core.exprScopes none expression) → ∀ nextEnv,
      nextEnv.mod = typingEnv.mod → nextEnv.vars = typingEnv.vars →
      nextEnv.impl = typingEnv.impl → nextEnv.inExpr = typingEnv.inExpr → ∀ state provenance,
      ExpressionReplayAt nextEnv { env with scopes := scope :: env.scopes } results vt target scopeCount
        expression state provenance) :
    BlockReplayAt typingEnv env results vt target scopeCount loop bindings want
      (.mk scope statements value) initial upper := by
  intro type start finish before after roots range typed replay ceiling scopes metadata values rootBounds stack ready generated loopBounds loopReplay native
  have parts := SourceScopesWithin.block_parts scopes
  have statementScopes := (SourceScopesWithin.statements_parent statements (some scope) none).mp parts.2.1
  apply ready.typedBlockTrackedNative loop (contextTypedResultUpper env.mod env.ctx) bindings want scope statements value
    typed replay ceiling parts.1
    (by
      intro binding member
      exact ⟨by simpa only [lowerEnv, Array.size_mapIdx] using (metadata binding member).1,
        (metadata binding member).2⟩)
    values (by
      intro binding member root rootMember
      rw [ready.slotsEq]
      exact rootBounds binding member root rootMember)
    generated loopBounds native
  · intro env1 env2 tn1 tn2 childBefore childAfter state provenance moduleEq variablesEq implEq modeEq
      childTyped childReplay childCeiling childReady entryEq childGenerated childNative
    have childStack : env1.inExpr = false → ∀ entered ∈ state.stack, entered < scopeCount := by
      intro outside entered member
      rw [entryEq, initialized_stack] at member
      rcases List.mem_cons.mp member with rfl | retained
      · exact parts.1
      · exact stack (modeEq.symm.trans outside) entered retained
    exact statementChild env1 moduleEq variablesEq implEq modeEq state provenance env2 tn1 tn2 childBefore childAfter
      childTyped childReplay childCeiling statementScopes childStack childReady childGenerated
      (loopBounds.mono (by
        rw [entryEq]
        exact Nat.le_trans
          (advB_emitEffect (.enter scope) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial _ _ rfl).ext.1
          (by
            have growth := (advB_initSlots bindings
              (lowerEnv env.mod env.impl.vars env.impl.results.toList)
              (Goose.Lower.pushScope scope (lowerEnv env.mod env.impl.vars env.impl.results.toList)
                (Goose.Lower.emitEffect (.enter scope)
                  (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2).2 _ _ rfl).ext.1
            simpa only [pushScope_run, Goose.Lower.emitEffect, Goose.Lower.curBlock, bind_run, get_apply, pure_run] using growth)))
      (by
        rw [entryEq]
        exact ((loopReplay.mono (advB_emitEffect (.enter scope) _ initial _ _ rfl)).pushScope parts.1).mono
          (advB_initSlots bindings _ _ _ _ rfl)) childNative
  · intro expression env2 tn2 childBefore state provenance moduleEq variablesEq implEq modeEq present
      childTyped childReplay childReady entryEq childGenerated childNative
    have expressionScopes : SourceScopesWithin scopeCount (Core.exprScopes none expression) := by
      apply (SourceScopesWithin.expression_parent expression (some scope) none).mp
      cases present
      exact parts.2.2
    exact expressionChild expression present expressionScopes env2 moduleEq variablesEq implEq modeEq state provenance
      type tn2 finish childBefore after roots childTyped childReplay ceiling childReady childGenerated childNative

#print axioms blockReplay_of_children

end Goose.Lower.Validation.SummaryPreservation
