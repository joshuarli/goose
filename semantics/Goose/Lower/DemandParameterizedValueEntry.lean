import Goose.Lower.DemandGeneratedOwner
import Goose.Lower.DemandParameterizedBlockBody
import Goose.Lower.DemandGeneratedBlockValue

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_parameterized_value_entry {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store })
    (canonical : ParameterizedBlockBodyAt source body) {expression : Expr} (hasValue : block.value = some expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before start : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile body.context.retained)
    (bounded : map.Bounded start.vals.size) {initial frame : GIR.Frame} {initialPoint point : Pt} {after : St}
    (realized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      ⟨initialPoint, initial, { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩)
    {fuel : Nat} (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) after)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx start initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point []) :
    ∃ child : ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression after,
      child.typingEnv = body.typingAfter ∧ child.rootsEnv = body.rootsEnv ∧
      body.ValueChildAt expression (canonical.value.trans hasValue) child ∧
      GeneratedSourceOwner selected child.context ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root child.path (.expression expression)
          (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block),
        GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required ∧
        map.Admitted cfg.mod.profile child.context.retained ∧
        map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block).vals.size ∧
        DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx child.world
          child.typingEnv child.rootsEnv child.context.inputFuture map.values map.runs ⟨point, frame, after⟩ := by
  have typed : tyExpr body.typingAfter expression body.typingEnd = .ok (source.ty, source.typingEnd) := by
    rw [canonical.typingAfter, canonical.typingEnd]
    have typed := source.typedValue
    rw [hasValue] at typed
    exact typed
  have rooted : rpExpr body.rootsEnv expression body.rootsEnd = .ok (source.roots, source.rootsEnd) := by
    rw [canonical.roots, canonical.rootsEnd]
    have rooted := source.rootedValue
    rw [hasValue] at rooted
    exact rooted
  have effects : EffLe source.rootsEnd.eff body.world.E := by rw [canonical.world]; exact source.effects
  obtain ⟨child, childTyping, childRoots, typeEq, childAt, _, childOccurrence, childRows, _, childAdmitted, childBounded, childDemand⟩ :=
    accepted_generated_block_value_entry body (canonical.value.trans hasValue) typed rooted effects statements bodyOccurrence
      canonical.all canonical.scope canonical.value bodyRows coverage admitted bounded realized post
  have bodyOwned : GeneratedSourceOwner selected body.context :=
    owned.transport canonical.plans.symm canonical.path.symm
      (by rw [canonical.scope, canonical.all, canonical.value]; cases block; rfl) canonical.context.symm
  have childOwned : GeneratedSourceOwner selected child.context :=
    (bodyOwned.child rfl body.all.length (.expression expression) .expression
      (by rw [canonical.value, hasValue]; exact blockValueChild) (by trivial)).transport
      childAt.plans.symm childAt.path.symm rfl childAt.context.symm
  exact ⟨child, childTyping, childRoots, childAt, childOwned, childOccurrence, childRows, childAdmitted, childBounded, childDemand⟩

#print axioms accepted_generated_parameterized_value_entry
end Goose.Lower
