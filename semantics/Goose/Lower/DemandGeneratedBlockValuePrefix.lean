import Goose.Lower.DemandGeneratedBlockSuffixPrefix
import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive GeneratedBlockValuePrefixDemand {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame)
    (cursor : ∀ {expression : Expr} {innerState : St},
      ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop) : DemandRuntimePoint → Prop
  | emitted {runtime : DemandRuntimePoint}
      (demanded : GeneratedClearBlockDemand source map required cx results before loop initial runtime) :
      GeneratedBlockValuePrefixDemand source selected map required before loop initial (@cursor) runtime
  | expression {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }} {expression : Expr} {valueState : St}
      {child : ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression valueState}
      {initialValue : GIR.Frame} {valuePoint : Pt} {fuel : Nat} {runtime : DemandRuntimePoint}
      (canonical : GeneratedBlockBodyAt source body) (hasValue : block.value = some expression)
      (childAt : body.ValueChildAt expression (canonical.value.trans hasValue) child)
      (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) valueState)
      (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) initialValue valuePoint [])
      (demanded : cursor child (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)
        (lowerExpr expression (lowerEnv cfg.mod env.vars results)
          (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block)).2
        initialValue valuePoint map required runtime) :
      GeneratedBlockValuePrefixDemand source selected map required before loop initial (@cursor) runtime

theorem accepted_generated_block_value_suffix_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 })
    (canonical : GeneratedBlockBodyAt source body) {expression : Expr} (hasValue : block.value = some expression)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] true block) before)
    (bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (bodyInput : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      cx results loop body.typingEnv body.rootsEnv
      (lowerStmts loop (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)).2
      { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1))
    {fuel : Nat} {addressed : DemandRuntimePoint}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) addressed.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) addressed.frame addressed.point [])
    (bodyBounded : map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block).vals.size)
    (bodyRealized : map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes } addressed)
    (extended : ExtT (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (cursor : ∀ {expression : Expr} {innerState : St},
      ExprSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (valueFamily : GeneratedExpressionPrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected loop expression (@cursor))
    {consumed taken : Nat} {reached : DemandRuntimePoint}
    (prefixSteps : DemandRuntimePrefix cx consumed ⟨start, initial, state⟩ addressed)
    (residual : DemandRuntimePrefix cx taken addressed reached) :
    DemandPrefixDecomposition cx (fun fuel => execBlock fuel cfg env [] block)
      (GeneratedBlockValuePrefixDemand source selected map required before loop initial (@cursor))
      (GeneratedBlockPrefixEnd source map required cx results before loop initial)
      (consumed + taken) ⟨start, initial, state⟩ reached := by
  let innerEnv : Env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }
  let le := lowerEnv cfg.mod env.vars results
  let valueStart := demandBlockValueBefore le before loop [] block
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
  obtain ⟨child, childTyping, childRoots, _, childAt⟩ := body.valueChild expression (canonical.value.trans hasValue)
    source.ty source.typingEnd source.roots source.rootsEnd typed rooted effects fuel .unit statements
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression expression) valueStart := by
    rw [childAt.path, canonical.all]
    exact .blockValue bodyOccurrence hasValue
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod body.rootsEnv.access (.blockValue bodyOccurrence hasValue) required :=
      .blockValue (valueAt := hasValue) bodyRows
    simpa only [childRoots, childAt.path, canonical.all, valueStart, le, demandBlockValueBefore] using inherited
  have bodyOwned : GeneratedSourceOwner selected body.context :=
    owned.transport canonical.plans.symm canonical.path.symm
      (by rw [canonical.scope, canonical.all, canonical.value]; cases block; rfl) canonical.context.symm
  have childOwned : GeneratedSourceOwner selected child.context :=
    (bodyOwned.child rfl body.all.length (.expression expression) .expression
      (by rw [canonical.value, hasValue]; exact blockValueChild) (by trivial)).transport
      childAt.plans.symm childAt.path.symm rfl childAt.context.symm
  have childRealized : map.Realizes cfg.mod child.world innerEnv addressed := by
    simpa only [RetainedSsaMap.Realizes, childAt.world] using bodyRealized
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    intro profile alias member
    apply childAt.retained alias
    rw [demandContextRetainedEq canonical.plans canonical.path
      (by rw [canonical.scope, canonical.all, canonical.value]; cases block; rfl) canonical.context]
    exact admitted profile alias member
  have currentEq : (lowerStmts loop (block.stmts.take body.offset) le
      (demandBlockStatementsBefore le before [] block)).2 = demandBlockStatementsBefore le before [] block := by
    simp only [canonical.offset, List.take_zero, lowerStmts, pure_run]
  have normalizedInput := bodyInput
  rw [currentEq] at normalizedInput
  obtain ⟨finalTyping, same, _, normal⟩ := (body.result fuel (.normal .unit) statements).frame
  have finalEq := normal .unit rfl
  subst finalTyping
  have childInput : GeneratedPrefixInput cfg innerEnv cx results loop child.typingEnv child.rootsEnv
      valueStart addressed.frame addressed.point := by
    refine ⟨?_, ?_, post.pp, post.rel, input.moduleEq, input.resultsEq, normalizedInput.depth,
      (by cases loop <;> exact input.targets), input.counter.afterPost post,
      normalizedInput.generated.lowerStmts loop block.stmts normalizedInput.frames.toTargets rfl,
      normalizedInput.frames.mono (advB_lowerStmts loop block.stmts _ _ _ _ rfl).ext⟩
    · apply normalizedInput.metadata.transport
      · rw [childTyping]; exact same.impl
      · rw [childRoots]
    · apply normalizedInput.loops.transport
      rw [childTyping]; exact same.loops
  have expressionExtended : ExtT (lowerExpr expression le valueStart).2 cx.fn.blocks := by
    have extension := generated_block_value_extended extended
    simpa only [hasValue, lowerBlockValue] using extension
  have valueProgress := valueFamily child childOwned childOccurrence childRows coverage childAdmitted bodyBounded
    childRealized childInput expressionExtended residual
  cases valueProgress.progress with
  | interior demanded => exact .interior (.expression canonical hasValue childAt statements post demanded)
  | @complete expressionFuel expressionConsumed expressionRemaining boundary value count expressionSteps remaining evaluated expressionEnd =>
    let common := max fuel expressionFuel
    have statementsRaised := ((monoAll fuel common (Nat.le_max_left _ _)).stmts cfg innerEnv block.stmts
      { state with nextScope := state.nextScope + 1 }).1 _ _ statements
    have evaluatedRaised := ((monoAll expressionFuel common (Nat.le_max_right _ _)).expr cfg innerEnv expression addressed.state).1 _ _ evaluated
    have valueDone : valueFlow common cfg block.value innerEnv (.normal .unit) addressed.state = .ok (.normal value) boundary.state := by
      rw [hasValue]
      simp only [valueFlow, bind_apply, evaluatedRaised, pure_apply]
    have combined : Post cfg innerEnv cx before initial
        (lowerBlockValue true block.value le valueStart).2 boundary.frame boundary.point
        [((lowerBlockValue true block.value le valueStart).1, .val value)] := by
      rw [hasValue]
      simpa only [lowerBlockValue, List.nil_append] using post.comp expressionEnd.post
    have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows combined.pp extended
    have leaveLabel : (match block.value with
        | some _ => (⟨source.path ++ [block.stmts.length], .expression, .exit⟩ : DemandSourceLabel)
        | none => ⟨source.path, .block, .exit⟩) = ⟨child.path, .expression, .exit⟩ := by
      rw [hasValue, childAt.path, canonical.path, canonical.all]
    have leaveDemand : GeneratedClearBlockDemand source map required cx results before loop initial boundary :=
      .valueExit canonical hasValue childAt statementsRaised evaluatedRaised (leaveLabel ▸ leaveSite) coverage expressionEnd.demanded
    have suffix := accepted_generated_block_leave_prefix source occurrence rows coverage admitted bounded realized statementsRaised
      valueDone combined extended leaveDemand (prefixSteps.append expressionSteps) remaining
    cases suffix with
    | interior demanded => exact .interior (.emitted demanded)
    | complete suffixCount prefixSteps residual evaluated post => exact .complete (by omega) prefixSteps residual evaluated post

end Goose.Lower
