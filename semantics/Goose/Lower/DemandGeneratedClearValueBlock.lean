import Goose.Lower.DemandGeneratedClearBlock

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_global_clear_value_block_traversal {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : GlobalClearStatements block.stmts)
    {type : IntTy} {number : Int} (hasValue : block.value = some (.lit type number))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] true block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩)
    (atPoint : before.pp = some point) (related : Rel cfg env cx frame before)
    (extended : ExtT (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {fuel : Nat} {addressedState : St}
    (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) addressedState) :
    ∃ after finalPoint finalFrame,
      DemandUniformTraversal cx (GeneratedClearBlockDemand source map required cx results before loop frame)
        (block.stmts.length * 2 + 3) ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      execBlock (fuel + 1) cfg env [] block state = .ok (.normal (.int type number)) after ∧
      Post cfg env cx before frame (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2
        finalFrame finalPoint [((lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).1, .val (.int type number))] ∧
      map.Realizes cfg.mod source.world env ⟨finalPoint, finalFrame, after⟩ ∧
      (∀ taken actualFuel reached, taken ≤ block.stmts.length * 2 + 3 →
        DemandPrefix cx taken actualFuel ⟨point, frame, state⟩ reached →
        GeneratedClearBlockDemand source map required cx results before loop frame reached) ∧
      ∀ taken reached, taken ≤ block.stmts.length * 2 + 3 →
        DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached →
        GeneratedClearBlockDemand source map required cx results before loop frame reached := by
  let le := lowerEnv cfg.mod env.vars results
  let innerEnv : Env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }
  let valueStart := demandBlockValueBefore le before loop [] block
  obtain ⟨body, canonical, bodyOccurrence, bodyRows, bodyAdmitted, bodyEndPoint, bodyEndFrame,
    prefixTrace, wholeBodyPost, bodyBounded, bodyRealized⟩ :=
    accepted_generated_global_clear_block_prefix source fragment occurrence rows coverage admitted bounded realized
      atPoint related extended statements
  have typed : tyExpr body.typingAfter (.lit type number) body.typingEnd = .ok (source.ty, source.typingEnd) := by
    rw [canonical.typingAfter, canonical.typingEnd]
    have typed := source.typedValue
    rw [hasValue] at typed
    exact typed
  have rooted : rpExpr body.rootsEnv (.lit type number) body.rootsEnd = .ok (source.roots, source.rootsEnd) := by
    rw [canonical.roots, canonical.rootsEnd]
    have rooted := source.rootedValue
    rw [hasValue] at rooted
    exact rooted
  have effects : EffLe source.rootsEnd.eff body.world.E := by rw [canonical.world]; exact source.effects
  obtain ⟨child, _, rootsEq, _, childCanonical⟩ := body.valueChild (.lit type number) (canonical.value.trans hasValue)
    source.ty source.typingEnd source.roots source.rootsEnd typed rooted effects fuel .unit statements
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression (.lit type number)) valueStart := by
    rw [childCanonical.path, canonical.all]
    exact .blockValue bodyOccurrence hasValue
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod body.rootsEnv.access (.blockValue bodyOccurrence hasValue) required :=
      .blockValue (valueAt := hasValue) bodyRows
    simpa only [rootsEq, childCanonical.path, canonical.all, valueStart, le, demandBlockValueBefore] using inherited
  have childRealized : map.Realizes cfg.mod child.world innerEnv ⟨bodyEndPoint, bodyEndFrame, addressedState⟩ := by
    simpa only [RetainedSsaMap.Realizes, childCanonical.world] using bodyRealized
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained :=
    fun profile alias member => childCanonical.retained alias (bodyAdmitted profile alias member)
  have valueExtended : ExtT (lowerExpr (.lit type number) le valueStart).2 cx.fn.blocks := by
    have extension := generated_block_value_extended extended
    simpa only [hasValue, lowerBlockValue] using extension
  have valueSite := GeneratedDemandInstruction.literal_auto childOccurrence childRows wholeBodyPost.pp valueExtended
  let valueRun := lowerExpr (.lit type number) le valueStart
  let valueFrame := bodyEndFrame.set valueRun.1 (.val (.int type number))
  let valuePoint : Pt := (bodyEndPoint.1, bodyEndPoint.2 + 1)
  have emitted : emitDef (.constInt type number) le valueStart = (valueRun.1, valueRun.2) := rfl
  have valuePost := (Post.def_leaf wholeBodyPost emitted valueExtended (.val (.int type number))).1
  have leafPost := (Post.def_leaf (Post.init wholeBodyPost.rel wholeBodyPost.pp) emitted valueExtended (.val (.int type number))).1
  have expressionDone : evalExpr fuel cfg innerEnv (.lit type number) addressedState = .ok (.int type number) addressedState := by
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at statements
    | succ fuel => simp only [evalExpr, pure_apply]
  have boundary := ExpressionDemandBoundary.of_result (child.result fuel (.int type number) expressionDone)
    childAdmitted bodyBounded childRealized leafPost
  have valueBuilder : lowerBlockValue true block.value le valueStart = valueRun := by rw [hasValue]; rfl
  have wholeValuePost : Post cfg innerEnv cx before frame (lowerBlockValue true block.value le valueStart).2
      valueFrame valuePoint [((lowerBlockValue true block.value le valueStart).1, .val (.int type number))] := by
    rw [valueBuilder]
    exact valuePost
  have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows wholeValuePost.pp extended
  have leaveLabel : (match block.value with
      | some _ => (⟨source.path ++ [block.stmts.length], .expression, .exit⟩ : DemandSourceLabel)
      | none => ⟨source.path, .block, .exit⟩) = ⟨child.path, .expression, .exit⟩ := by
    rw [hasValue, childCanonical.path, canonical.path, canonical.all]
  let finalState : St := { addressedState with store := releaseVars env.vars env.act block.scope state.nextScope env.vars.size addressedState.store }
  let finalFrame : GIR.Frame := { valueFrame with scopes := env.scopes }
  let finalPoint : Pt := (valuePoint.1, valuePoint.2 + 1)
  have leaveRun : execEff cx.fn valueFrame (.leave block.scope) addressedState = .ok finalFrame finalState :=
    block_leave_exec (env := env) (scope := block.scope) (instanceId := state.nextScope) wholeValuePost.rel addressedState
  have leaveStep : Evidence.RuntimeStep cx.cfg cx.fn valuePoint valueFrame addressedState finalPoint finalFrame finalState :=
    .effect leaveSite.instruction leaveRun
  have valueFlowDone : valueFlow fuel cfg block.value innerEnv (.normal .unit) addressedState =
      .ok (.normal (.int type number)) addressedState := by
    rw [hasValue]
    change (evalExpr fuel cfg innerEnv (.lit type number) >>= fun value => pure (Flow.normal value)) addressedState = _
    simp only [bind_apply, expressionDone, pure_apply]
  obtain ⟨_, _, _, _, evaluatedBlock, finalPost, _, _, finalDemand⟩ :=
    accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized statements
      valueFlowDone wholeValuePost extended leaveStep
  let valid := GeneratedClearBlockDemand source map required cx results before loop frame
  have valueEntry : valid ⟨bodyEndPoint, bodyEndFrame, addressedState⟩ :=
    .valueEntry canonical hasValue childCanonical statements valueSite coverage
      ⟨⟨_, wholeBodyPost.pp, wholeBodyPost.rel⟩, child.frame, childRealized⟩
  have valueExit : valid ⟨valuePoint, valueFrame, addressedState⟩ :=
    .valueExit canonical hasValue childCanonical statements expressionDone (leaveLabel ▸ leaveSite) coverage boundary.demanded
  have ending : DemandUniformTraversal cx valid 2 ⟨bodyEndPoint, bodyEndFrame, addressedState⟩
      ⟨finalPoint, finalFrame, finalState⟩ :=
    .next valueEntry (fun fuel => .definition valueSite.instruction (by simp only [execOp, execPure, pure_apply]))
      (.next valueExit (fun fuel => .effect leaveSite.instruction leaveRun)
        (.done (.exit finalPost (source.result (fuel + 1) (.normal (.int type number)) evaluatedBlock) coverage finalDemand)))
  have traversal : DemandUniformTraversal cx valid (block.stmts.length * 2 + 3)
      ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, finalState⟩ := by
    simpa only [Nat.add_assoc] using prefixTrace.append ending
  refine ⟨finalState, finalPoint, finalFrame, traversal, evaluatedBlock, ?_, finalDemand.operands,
    fun taken actualFuel reached bound tracePrefix => traversal.prefix_invariant bound tracePrefix,
    fun taken reached bound steps => traversal.runtimePrefix_invariant bound steps⟩
  change Post cfg env cx before frame (lowerBlock loop [] true block le before).2 _ _
    [((lowerBlock loop [] true block le before).1, .val (.int type number))]
  rw [generated_block_value_result]
  exact finalPost

end Goose.Lower
