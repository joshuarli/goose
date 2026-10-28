import Goose.Lower.DemandParameterizedValueEntry
import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_parameterized_value_input {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St}
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store })
    {expression : Expr}
    {after : St} (child : ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression after)
    (childTyping : child.typingEnv = body.typingAfter) (childRoots : child.rootsEnv = body.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {initial frame : GIR.Frame} {start point : Pt}
    (input : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results loop
      body.typingEnv body.rootsEnv (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial start)
    {fuel : Nat} (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) after)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point []) :
    GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results loop
      child.typingEnv child.rootsEnv (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point := by
  obtain ⟨finalTyping, same, _, normal⟩ := (body.result fuel (.normal .unit) statements).frame
  have finalEq := normal .unit rfl
  subst finalTyping
  refine ⟨?_, ?_, post.pp, post.rel, input.moduleEq, input.resultsEq, input.depth,
    (by cases loop <;> exact input.targets), input.counter.afterPost post, ?_, ?_⟩
  · apply input.metadata.transport
    · rw [childTyping]; exact same.impl
    · rw [childRoots]
  · apply input.loops.transport
    rw [childTyping]; exact same.loops
  · simpa [demandBlockValueBefore] using
      input.generated.lowerStmts loop block.stmts input.frames.toTargets rfl
  · simpa [demandBlockValueBefore] using
      input.frames.mono (advB_lowerStmts loop block.stmts _ _ _ _ rfl).ext

#print axioms generated_parameterized_value_input
end Goose.Lower
