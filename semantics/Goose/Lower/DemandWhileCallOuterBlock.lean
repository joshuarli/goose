import Goose.Lower.DemandCallLoopNormal
import Goose.Lower.DemandCallLoopMixedNormal
import Goose.Lower.DemandWhileScalarCallAgreement
import Goose.Lower.DemandReachableBranchBlock

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_while_scalar_call_outer_block {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : block.stmts = [.while condition body loopOrigin]) (outerNoValue : block.value = none)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: (block.scope, state.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] false block (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      GeneratedGenericBranchBlockDecomposition source (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results)
        selected map required before none initial start
        (@WhileCallStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results root owner selected)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before none initial start taken reached stop after) := by
  let innerEnv : Env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩
  have agreement := accepted_generated_while_scalar_call_agreement (env := innerEnv) (loop := none) selected condition body loopOrigin conditionForm fragment noValue
  have nilPrefix : ReachableSequencePrefixFamily (env := innerEnv) cx results selected before none [] false block []
      (@WhileCallStatementCursor cfg innerEnv caller results root owner selected) :=
    GeneratedSequencePrefixFamily.reachable (env := innerEnv) (cx := cx) (selected := selected) (before := before) (loop := none)
      (bindings := []) (want := false) (block := block) (statements := [])
      (cursor := @WhileCallStatementCursor cfg innerEnv caller results root owner selected)
      (fun {state} => accepted_generated_sequence_prefix_nil selected before none [] false block _ (state := state))
  have nilStopped : ReachableStoppedSequencePrefixFamily (env := innerEnv) cx results selected before none [] false block [] :=
    GeneratedStoppedSequencePrefixFamily.reachable (env := innerEnv) (cx := cx) (selected := selected) (before := before) (loop := none)
      (bindings := []) (want := false) (block := block) (statements := [])
      (fun {state} => accepted_generated_stopped_sequence_nil selected before none [] false block (state := state))
  have prefixFamily : ReachableSequencePrefixFamily (env := innerEnv) cx results selected before none [] false block
      [.while condition body loopOrigin] (@WhileCallStatementCursor cfg innerEnv caller results root owner selected) :=
    fun {state} => accepted_generated_reachable_sequence_prefix_cons (env := innerEnv) selected before none [] false block _ agreement.1 nilPrefix (state := state)
  have stoppedFamily : ReachableStoppedSequencePrefixFamily (env := innerEnv) cx results selected before none [] false block
      [.while condition body loopOrigin] :=
    fun {state} => accepted_generated_reachable_stopped_sequence_cons (env := innerEnv) selected before none [] false block agreement.2 nilStopped (state := state)
  have normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg innerEnv block.stmts innerState = .ok flow after → flow = .normal .unit := by
    intro fuel innerState after flow done
    rw [outerStatements] at done
    exact scalar_call_loop_statement_normal (fragment St.initial) noValue done
  constructor
  · intro taken reached steps
    exact accepted_generated_reachable_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended _
      (by rw [outerStatements]; exact prefixFamily) normal outerNoValue entry steps
  · intro taken reached steps targetFuel stop after stopped nonTimeout
    exact accepted_generated_reachable_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
      (by rw [outerStatements]; exact stoppedFamily) normal outerNoValue entry steps stopped nonTimeout


theorem accepted_generated_while_call_outer_block {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : block.stmts = [.while condition body loopOrigin]) (outerNoValue : block.value = none)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (contextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (implAt : cfg.mod.impls[calleeContext.impl]? = some callee) (depth : env.depth < maxCallDepth)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := env.depth + 1 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: (block.scope, state.nextScope) :: env.scopes }
      (.expr (.call callContext arguments callOrigin) statementOrigin) innerState), CallMixedArguments argumentSource.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { env with scopes := (body.scope, middle.nextScope) :: (block.scope, state.nextScope) :: env.scopes }
      (.expr (.call callContext arguments callOrigin) statementOrigin) innerState), CallMixedStoppedArguments argumentSource.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.block none [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none [] false block (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      GeneratedGenericBranchBlockDecomposition source (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results)
        selected map required before none initial start
        (@WhileCallStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results root owner selected)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before none initial start taken reached stop after) := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: (block.scope, state.nextScope) :: env.scopes } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single contextAt implAt depth fragment form hasValue shrink
      (argumentsForm middle) (stoppedArgumentsForm middle)
  exact accepted_generated_while_scalar_call_outer_block source condition body loopOrigin conditionForm outerStatements outerNoValue
    mixed noValue selected owned occurrence rows coverage admitted bounded realized input extended entry

theorem GeneratedGenericBlockPrefixDemand.whileCall_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) source selected map required before none initial
      (@WhileCallStatementCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results root owner selected)
      (GeneratedBranchBlockEffectDemand source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before none initial) runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement innerState child before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_maximal_terminal terminal maximal

#print axioms GeneratedGenericBlockPrefixDemand.whileCall_excludes_maximal_terminal

#print axioms accepted_generated_while_scalar_call_outer_block
#print axioms accepted_generated_while_call_outer_block
end Goose.Lower
