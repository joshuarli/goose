import Goose.Lower.DemandParameterizedValueInput
import Goose.Lower.DemandControlProgressCursor
import Goose.Lower.DemandControlStatementAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_parameterized_value_progress {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store })
    (canonical : ParameterizedBlockBodyAt source body) {expression : Expr} (hasValue : block.value = some expression)
    (form : ControlPrefixExpression expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile body.context.retained)
    (bounded : map.Bounded (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).vals.size)
    {initial frame : GIR.Frame} {start point : Pt} {after : St}
    (realized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      ⟨start, initial, { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩)
    (input : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results loop
      body.typingEnv body.rootsEnv (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial start)
    {fuel : Nat} (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) after)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point [])
    (extended : ExtT (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, after⟩ reached) :
    ∃ child : ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression after,
      body.ValueChildAt expression (canonical.value.trans hasValue) child ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root child.path (.expression expression)
          (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block),
      ∃ childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required,
        GeneratedExpressionPrefixDecomposition child selected childOccurrence childRows map frame point
          (GeneratedControlProgressCursor cx child
            (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)
            (lowerExpr expression (lowerEnv cfg.mod env.vars results)
              (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).2
            frame point map required) taken reached := by
  obtain ⟨child, childTyping, childRoots, childAt, childOwned, childOccurrence, childRows,
    childAdmitted, childBounded, childDemand⟩ :=
    accepted_generated_parameterized_value_entry source body canonical hasValue selected owned bodyOccurrence bodyRows
      coverage admitted bounded realized statements post
  have childInput := generated_parameterized_value_input body child childTyping childRoots input statements post
  have valueExtended : ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results)
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).2 cx.fn.blocks := by
    have extension := generated_block_value_extended extended
    simpa only [hasValue, lowerBlockValue] using extension
  have progress := accepted_generated_control_progress_prefix_family (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
    selected loop form child childOwned childOccurrence childRows
    coverage childAdmitted childBounded childDemand.operands childInput valueExtended steps
  exact ⟨child, childAt, childOccurrence, childRows, progress⟩

theorem accepted_generated_parameterized_value_stopped {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store })
    (canonical : ParameterizedBlockBodyAt source body) {expression : Expr} (hasValue : block.value = some expression)
    (form : ControlPrefixExpression expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile body.context.retained)
    (bounded : map.Bounded (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).vals.size)
    {initial frame : GIR.Frame} {start point : Pt} {after : St}
    (realized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      ⟨start, initial, { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩)
    (input : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results loop
      body.typingEnv body.rootsEnv (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial start)
    {fuel : Nat} (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) after)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block) initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block) frame point [])
    (extended : ExtT (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨point, frame, after⟩ reached)
    {targetFuel : Nat} {stop : Stop} {final : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop final) (nonTimeout : stop ≠ .timeout) :
    ∃ child : ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression after,
      body.ValueChildAt expression (canonical.value.trans hasValue) child ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root child.path (.expression expression)
          (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block),
      GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required ∧
      StoppedExpressionPrefix child map cx results
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)
        frame point taken reached stop final := by
  obtain ⟨child, childTyping, childRoots, childAt, childOwned, childOccurrence, childRows,
    childAdmitted, childBounded, childDemand⟩ :=
    accepted_generated_parameterized_value_entry source body canonical hasValue selected owned bodyOccurrence bodyRows
      coverage admitted bounded realized statements post
  have childInput := generated_parameterized_value_input body child childTyping childRoots input statements post
  have valueExtended : ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results)
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop bindings block)).2 cx.fn.blocks := by
    have extension := generated_block_value_extended extended
    simpa only [hasValue, lowerBlockValue] using extension
  have progress := accepted_generated_read_stopped_expressions (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
    selected loop form.stopped child childOwned childOccurrence childRows
    coverage childAdmitted childBounded childDemand.operands childInput valueExtended steps stopped nonTimeout
  exact ⟨child, childAt, childOccurrence, childRows, progress⟩

#print axioms accepted_generated_parameterized_value_stopped

#print axioms accepted_generated_parameterized_value_progress
end Goose.Lower
