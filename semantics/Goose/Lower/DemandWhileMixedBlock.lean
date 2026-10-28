import Goose.Lower.DemandWhileMixedStatements

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_mixed_unit_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : WhileMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    (noValue : block.value = none) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedBlockPrefixDecomposition source selected map required before none initial start
      (GeneratedGenericBlockPrefixDemand source selected map required before none initial
        (@WhileMixedStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results root owner selected)
        (GeneratedClearBlockDemand source map required cx results before none initial)) taken reached := by
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before none [] true block block.stmts
      (@WhileMixedStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results root owner selected) :=
    (accepted_generated_while_mixed_statements
    (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) fragment selected before [] true block).1
  apply accepted_generated_generic_block_prefix source selected owned occurrence rows coverage admitted bounded
    realized input extended _ bodyFamily (fun done => fragment.normal done) (GeneratedClearBlockDemand source map required cx results before none initial) ?_ steps
  intro body canonical bodyOccurrence bodyRows bodyInput fuel addressed statements post bodyBounded bodyRealized consumed taken reached prefixSteps residual
  exact accepted_generated_block_unit_suffix_prefix source body canonical noValue occurrence bodyOccurrence rows bodyRows
    coverage admitted bounded realized statements post bodyBounded bodyRealized extended prefixSteps residual


theorem accepted_generated_while_mixed_value_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : WhileMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {expression : Expr} (hasValue : block.value = some expression) (valueForm : ControlPrefixExpression expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedBlockPrefixDecomposition source selected map required before none initial start
      (GeneratedGenericBlockPrefixDemand source selected map required before none initial
        (@WhileMixedStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results root owner selected)
        (GeneratedBlockValuePrefixDemand source selected map required before none initial
          (@CanonicalExpressionPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx))) taken reached := by
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before none [] true block block.stmts
      (@WhileMixedStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results root owner selected) :=
    (accepted_generated_while_mixed_statements
    (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) fragment selected before [] true block).1
  apply accepted_generated_generic_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended
    _ bodyFamily (fun done => fragment.normal done)
    (GeneratedBlockValuePrefixDemand source selected map required before none initial
      (@CanonicalExpressionPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx)) ?_ steps
  intro body canonical bodyOccurrence bodyRows bodyInput fuel addressed statements post bodyBounded bodyRealized consumed taken reached prefixSteps residual
  exact accepted_generated_block_value_suffix_prefix source body canonical hasValue selected owned occurrence bodyOccurrence rows bodyRows
    coverage admitted bounded realized input bodyInput statements post bodyBounded bodyRealized extended _
      (fun {innerState} => accepted_generated_control_prefix_family
        (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected none valueForm) prefixSteps residual



theorem accepted_generated_while_mixed_unit_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (fragment : WhileMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts) (noValue : block.value = none)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedUnitBlockPrefix source map required cx results before initial start taken reached stop after := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before none [] true block block.stmts :=
    (accepted_generated_while_mixed_statements
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) fragment selected before [] true block).2
  exact accepted_generated_generic_unit_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily (fun done => fragment.normal done) noValue steps stopped nonTimeout

theorem accepted_generated_while_mixed_value_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (fragment : WhileMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts) {expression : Expr} (hasValue : block.value = some expression)
    (valueForm : ControlPrefixExpression expression)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedValueBlockSuffix source map required cx results before none initial start taken reached stop after := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before none [] true block block.stmts :=
    (accepted_generated_while_mixed_statements
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) fragment selected before [] true block).2
  exact accepted_generated_generic_value_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily (fun done => fragment.normal done) hasValue valueForm steps stopped nonTimeout



#print axioms accepted_generated_while_mixed_unit_block_prefix
#print axioms accepted_generated_while_mixed_value_block_prefix
#print axioms accepted_generated_while_mixed_unit_block_stopped
#print axioms accepted_generated_while_mixed_value_block_stopped
end Goose.Lower
