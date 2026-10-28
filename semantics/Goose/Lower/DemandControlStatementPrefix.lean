import Goose.Lower.DemandShortCircuitPrefixFamily
import Goose.Lower.DemandGeneratedExpressionStatementPrefix
import Goose.Lower.DemandGeneratedBlockPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ControlStatementPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | clear {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : GeneratedGlobalClearPrefixCursor cx results source before built initial start map required runtime) :
      ControlStatementPrefixCursor cx results source before built initial start map required runtime
  | expression {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : GeneratedExpressionStatementPrefixCursor (@CanonicalExpressionPrefixCursor cfg env cx)
        source before built initial start map required runtime) :
      ControlStatementPrefixCursor cx results source before built initial start map required runtime

theorem GeneratedStatementPrefixFamily.mapCursor {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {loop : Option LoopCtx} {statement : Stmt}
    {cursor next : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : GeneratedStatementPrefixFamily cx results selected loop statement cursor)
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime) :
    GeneratedStatementPrefixFamily cx results selected loop statement next := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have decomposition := family source owned occurrence rows coverage admitted bounded realized input extended steps
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior demanded => exact .interior (convert source demanded)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

inductive ControlStatements : List Stmt → Prop
  | nil : ControlStatements []
  | clear (global : GlobalId) (origin : OriginId) {rest : List Stmt} (tail : ControlStatements rest) :
      ControlStatements (.clear (.global global) origin :: rest)
  | expression {expression : Expr} (origin : OriginId) (form : ControlPrefixExpression expression)
      {rest : List Stmt} (tail : ControlStatements rest) : ControlStatements (.expr expression origin :: rest)

theorem accepted_generated_control_statements_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : ControlStatements statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
      (@ControlStatementPrefixCursor cfg env cx results) := by
  induction fragment with
  | nil => exact accepted_generated_sequence_prefix_nil selected before loop bindings want block _
  | clear global origin tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.clear (.global global) origin)
        (@ControlStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_global_clear_prefix_family selected loop global origin)
      intro statement state source before built initial start map required runtime cursor
      exact .clear cursor
    intro state
    exact accepted_generated_sequence_prefix_cons selected before loop bindings want block _ head ih
  | @expression expression origin form rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.expr expression origin)
        (@ControlStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_expression_statement_prefix selected loop _ origin _
          (accepted_generated_control_prefix_family selected loop form))
      intro statement state source before built initial start map required runtime cursor
      exact .expression cursor
    intro state
    exact accepted_generated_sequence_prefix_cons selected before loop bindings want block _ head ih

theorem ControlStatementPrefixCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ControlStatementPrefixCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | clear cursor =>
    obtain ⟨_, _, _, demanded⟩ := cursor.frame
    exact demanded.operands
  | expression cursor =>
    cases cursor with
    | expression metadata demanded => simpa only [metadata.world] using demanded.carried

theorem GeneratedSequencePrefixCursor.control_realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@ControlStatementPrefixCursor cfg env cx results)
      map required cx results before loop bindings block selected source initial runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  induction cursor with
  | head canonical owned occurrence rows coverage demanded =>
    simpa only [canonical.world] using demanded.realizes
  | tail canonical evaluated prefixSteps post demanded ih =>
    simpa only [canonical.world] using ih

theorem accepted_generated_control_block_statements_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
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
    (fragment : ControlStatements block.stmts)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    (taken = 0 ∧ reached = ⟨start, initial, state⟩ ∧
      GeneratedClearBlockDemand source map required cx results before loop initial reached) ∨
      GeneratedBlockStatementsPrefix (before := before) (loop := loop) source selected map required initial start
        (@ControlStatementPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) taken reached := by
  have family : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] true block block.stmts
      (@ControlStatementPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) :=
    fun {innerState} => accepted_generated_control_statements_prefix
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected before loop [] true block fragment
  exact accepted_generated_block_statements_prefix source selected owned occurrence rows coverage admitted bounded
    realized input extended _ family steps

#print axioms accepted_generated_control_block_statements_prefix
#print axioms accepted_generated_control_statements_prefix
#print axioms GeneratedSequencePrefixCursor.control_realizes

end Goose.Lower
