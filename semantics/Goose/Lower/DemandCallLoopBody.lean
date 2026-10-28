import Goose.Lower.DemandReachableBranchBlock
import Goose.Lower.DemandCallReachableSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem call_expression_single_normal {cfg : Cfg} {env : Env} {context : ContextId} {arguments : List Arg}
    {origin statementOrigin : OriginId} {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env [.expr (.call context arguments origin) statementOrigin] state = .ok flow after) :
    flow = .normal .unit := by
  cases fuel with
  | zero => simp [execStmts, timeout, M.stop] at done
  | succ fuel =>
    cases fuel with
    | zero => simp [execStmts, execStmt, bind_apply, timeout, M.stop] at done
    | succ fuel =>
      cases evaluated : evalExpr fuel cfg env (.call context arguments origin) state with
      | stop reason final =>
        simp only [execStmts, execStmt, bind_apply, Functor.map, bind_apply, evaluated, pure_apply] at done
        cases done
      | ok value middle =>
        simp only [execStmts, execStmt, bind_apply, Functor.map, bind_apply, evaluated, pure_apply] at done
        exact (Res.ok.inj done).1.symm

theorem accepted_generated_call_loop_body {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    {context : ContextId} {arguments : List Arg} {origin statementOrigin : OriginId}
    (bodyStatements : block.stmts = [.expr (.call context arguments origin) statementOrigin]) (noValue : block.value = none)
    {ctx : Context} {impl : Impl} (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl) (depth : env.depth < maxCallDepth)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := middle.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := env.depth + 1 } impl.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : impl.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.expr (.call context arguments origin) statementOrigin) innerState),
      CallMixedArguments child.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ {innerState : St} (child : StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.expr (.call context arguments origin) statementOrigin) innerState),
      CallMixedStoppedArguments child.rootsEnv.access arguments)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      GeneratedGenericBranchBlockDecomposition source (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected map required before loop initial start
        (@ReachableCallStatementFamilyCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial start taken reached stop after) := by
  have families := accepted_generated_reachable_control_call_single
    (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
    contextAt implAt depth fragment form hasValue shrink argumentsForm stoppedArgumentsForm selected before loop [] false block
  have normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit := by
    intro fuel innerState after flow done
    rw [bodyStatements] at done
    exact call_expression_single_normal done
  constructor
  · intro taken reached steps
    apply accepted_generated_reachable_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended _
      (by rw [bodyStatements]; exact fun {state} => families.1 (state := state)) normal noValue entry steps
  · intro taken reached steps targetFuel stop after stopped nonTimeout
    exact accepted_generated_reachable_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
      (by rw [bodyStatements]; exact fun {state} => families.2 (state := state)) normal noValue entry steps stopped nonTimeout

#print axioms accepted_generated_call_loop_body

#print axioms call_expression_single_normal
end Goose.Lower
