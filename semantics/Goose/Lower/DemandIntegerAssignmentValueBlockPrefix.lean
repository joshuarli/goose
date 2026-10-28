import Goose.Lower.DemandIntegerAssignmentBlockPrefix
import Goose.Lower.DemandControlValueBlockPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_integer_assignment_value_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : IntegerAssignmentStatements block.stmts)
    {expression : Expr} (hasValue : block.value = some expression) (valueForm : ControlPrefixExpression expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedBlockPrefixDecomposition source selected map required before loop initial start
      (GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial
        (GeneratedBlockValuePrefixDemand source selected map required before loop initial
          (@CanonicalExpressionPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx))) taken reached := by
  apply accepted_generated_integer_assignment_block_prefix source fragment selected owned occurrence rows coverage admitted bounded realized input extended
    (GeneratedBlockValuePrefixDemand source selected map required before loop initial
      (@CanonicalExpressionPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx)) ?_ steps
  intro body canonical bodyOccurrence bodyRows bodyInput fuel addressed statements post bodyBounded bodyRealized consumed taken reached prefixSteps residual
  exact accepted_generated_block_value_suffix_prefix source body canonical hasValue selected owned occurrence bodyOccurrence rows bodyRows
    coverage admitted bounded realized input bodyInput statements post bodyBounded bodyRealized extended _
      (fun {innerState} => accepted_generated_control_prefix_family
        (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected loop valueForm) prefixSteps residual

#print axioms accepted_generated_integer_assignment_value_block_prefix

end Goose.Lower
