import Goose.Lower.DemandGeneratedClearSequence
import Goose.Lower.DemandGeneratedBlockUnit
import Goose.Lower.DemandGeneratedBlockLeave
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedBlockBodyAt {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 }) : Prop where
  world : body.world = source.world
  plans : body.plans = source.plans
  path : body.path = source.path
  scope : body.scope = block.scope
  all : body.all = block.stmts
  value : body.value = block.value
  offset : body.offset = 0
  context : HEq body.context source.context
  roots : body.rootsEnv = { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
  typingAfter : body.typingAfter = source.typingAfter
  typingEnd : body.typingEnd = source.typingValue
  rootsEnd : body.rootsEnd = source.rootsValue

inductive GeneratedClearBlockDemand {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (map required : RetainedSsaMap) (cx : FnCtx)
    (results : List Ty) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame) : DemandRuntimePoint → Prop
  | entry {point : Pt}
      (site : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path, .block, .entry⟩ point (.eff (.enter block.scope)))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.inputFuture
        map.values map.runs ⟨point, initial, state⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, initial, state⟩
  | body {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }} {runtime : DemandRuntimePoint}
      (canonical : GeneratedBlockBodyAt source body)
      (demanded : GeneratedClearSequenceDemand map required cx results before loop [] block body runtime) :
      GeneratedClearBlockDemand source map required cx results before loop initial runtime
  | unitEntry {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }}
      {point : Pt} {frame : GIR.Frame} {addressedState : St} {id : ValueId}
      (canonical : GeneratedBlockBodyAt source body)
      (site : GeneratedBlockUnitInstruction cfg.mod body.rootsEnv.access cx.fn required
        ⟨body.path, .block, .exit⟩ point (.def id .constUnit))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx body.world body.typingAfter body.rootsEnv (blockSuffixFuture body.context body.all.length)
        map.values map.runs ⟨point, frame, addressedState⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, frame, addressedState⟩
  | leave {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }}
      {point : Pt} {frame : GIR.Frame} {addressedState : St}
      (canonical : GeneratedBlockBodyAt source body)
      (site : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path, .block, .exit⟩ point (.eff (.leave block.scope)))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx body.world body.typingAfter body.rootsEnv (blockSuffixFuture body.context body.all.length)
        map.values map.runs ⟨point, frame, addressedState⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, frame, addressedState⟩
  | valueEntry {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }}
      {expression : Expr} {valueState : St} {child : ExprSource cfg
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression valueState}
      {point : Pt} {frame : GIR.Frame} {id : ValueId} {operation : Op} {fuel : Nat}
      (canonical : GeneratedBlockBodyAt source body) (hasValue : block.value = some expression)
      (childCanonical : body.ValueChildAt expression (canonical.value.trans hasValue) child)
      (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) valueState)
      (site : GeneratedDemandInstruction cfg.mod child.rootsEnv.access cx.fn required
        ⟨child.path, .expression, .entry⟩ point (.def id operation))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx child.world child.typingEnv child.rootsEnv child.context.inputFuture map.values map.runs ⟨point, frame, valueState⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, frame, valueState⟩
  | valueExit {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }}
      {expression : Expr} {valueState after : St} {child : ExprSource cfg
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } expression valueState}
      {point : Pt} {frame : GIR.Frame} {value : Val} {fuel : Nat}
      (canonical : GeneratedBlockBodyAt source body) (hasValue : block.value = some expression)
      (childCanonical : body.ValueChildAt expression (canonical.value.trans hasValue) child)
      (statements : execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 } = .ok (.normal .unit) valueState)
      (evaluated : evalExpr fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        expression valueState = .ok value after)
      (site : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨child.path, .expression, .exit⟩ point (.eff (.leave block.scope)))
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx child.world child.typingEnv child.rootsEnv child.context.outputFuture map.values map.runs ⟨point, frame, after⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, frame, after⟩
  | exit {point : Pt} {frame : GIR.Frame} {after : St} {id : ValueId} {value : Val}
      (post : Post cfg env cx before initial (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2
        frame point [(id, .val value)])
      (result : BlockResult source (.normal value) after)
      (coverage : map.Covers required)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨point, frame, after⟩) :
      GeneratedClearBlockDemand source map required cx results before loop initial ⟨point, frame, after⟩

theorem GeneratedClearBlockDemand.frame {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {map required : RetainedSsaMap} {cx : FnCtx}
    {results : List Ty} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (valid : GeneratedClearBlockDemand source map required cx results before loop initial runtime) :
    ∃ typing roots future,
      DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime ∨
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx source.world typing roots future map.values map.runs runtime := by
  cases valid with
  | entry site coverage demanded => exact ⟨_, _, _, Or.inl demanded⟩
  | body canonical demanded =>
    obtain ⟨typing, roots, future, framed⟩ := demanded.frame
    exact ⟨typing, roots, future, Or.inr (by simpa only [canonical.world] using framed)⟩
  | unitEntry canonical site coverage demanded =>
    exact ⟨_, _, _, Or.inr (by simpa only [canonical.world] using demanded)⟩
  | leave canonical site coverage demanded =>
    exact ⟨_, _, _, Or.inr (by simpa only [canonical.world] using demanded)⟩
  | valueEntry canonical hasValue childCanonical statements site coverage demanded =>
    exact ⟨_, _, _, Or.inr (by simpa only [childCanonical.world, canonical.world] using demanded)⟩
  | valueExit canonical hasValue childCanonical statements evaluated site coverage demanded =>
    exact ⟨_, _, _, Or.inr (by simpa only [childCanonical.world, canonical.world] using demanded)⟩
  | exit post result coverage demanded => exact ⟨_, _, _, Or.inl demanded⟩

theorem accepted_generated_global_clear_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : GlobalClearStatements block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    {loop : Option LoopCtx}
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
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 },
      GeneratedBlockBodyAt source body ∧
    ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root body.path (.block loop [] true block) before,
      GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required ∧
      map.Admitted cfg.mod.profile body.context.retained ∧
    ∃ bodyEndPoint bodyEndFrame,
      DemandUniformTraversal cx (GeneratedClearBlockDemand source map required cx results before loop frame)
        (block.stmts.length * 2 + 1) ⟨point, frame, state⟩ ⟨bodyEndPoint, bodyEndFrame, addressedState⟩ ∧
      Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before frame
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block) bodyEndFrame bodyEndPoint [] ∧
      map.Bounded (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before loop [] block).vals.size ∧
      map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        ⟨bodyEndPoint, bodyEndFrame, addressedState⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let innerEnv : Env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }
  let enteredFrame : GIR.Frame := { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
  let enteredState : St := { state with nextScope := state.nextScope + 1 }
  let enteredPoint : Pt := (point.1, point.2 + 1)
  let bodyBefore := demandBlockStatementsBefore le before [] block
  have enterSite := GeneratedDemandInstruction.blockEnter_auto occurrence rows atPoint extended
  have enterRun : execEff cx.fn frame (.enter block.scope) state = .ok enteredFrame enteredState := by
    simp only [execEff, freshScope, bind_apply, pure_apply, enteredFrame, enteredState]
  have enterStep : Evidence.RuntimeStep cx.cfg cx.fn point frame state enteredPoint enteredFrame enteredState :=
    .effect enterSite.instruction enterRun
  obtain ⟨_, entryDemand, _, _, _, _, _, bodyPoint, bodyRelated, _, _⟩ :=
    accepted_generated_block_enter_runtime_step source occurrence rows coverage bounded atPoint related realized extended enterStep
  obtain ⟨body, _, bodyTypingAfter, bodyRoots, bodyWorld, _, _, bodyTypingEnd, _, bodyRootsEnd, bodyPlans, bodyPath, bodyScope,
    bodyAll, bodyValue, bodyOffset, bodyContext, bodyOccurrence, bodyRows, _, bodyAdmitted, _, bodyDemand⟩ :=
    accepted_generated_body_entry source occurrence rows coverage admitted (show PreRel frame [] [] from trivial)
      realized bodyPoint bodyRelated
  have bodyCanonical : GeneratedBlockBodyAt source body :=
    ⟨bodyWorld, bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext, bodyRoots, bodyTypingAfter, bodyTypingEnd, bodyRootsEnd⟩
  have enteredValues : bodyBefore.vals.size = before.vals.size := by
    have values := (emitEffect_facts (show emitEffect (.enter block.scope) le before =
      ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)
      atPoint (generated_block_enter_extended extended)).1
    simpa only [bodyBefore, demandBlockStatementsBefore, initSlots, pure_run] using values
  have enteredPost : Post cfg innerEnv cx before frame bodyBefore enteredFrame enteredPoint [] :=
    ⟨bodyPoint, by simp, by simp, Nat.le_of_eq enteredValues.symm, fun _ _ => rfl, bodyRelated⟩
  have currentEq : (lowerStmts loop (block.stmts.take body.offset) le bodyBefore).2 = bodyBefore := by
    simp only [bodyOffset, List.take_zero, lowerStmts, pure_run]
  obtain ⟨bodyEndPoint, bodyEndFrame, bodyTrace, bodyPost, bodyBounded, bodyRealized⟩ :=
    accepted_generated_global_clears_traversal fragment body statements bodyOccurrence bodyAll bodyScope bodyValue
      bodyRows coverage bodyAdmitted (by rw [currentEq, enteredValues]; exact bounded) bodyDemand.operands
      (by rw [currentEq]; exact bodyPoint) (by rw [currentEq]; exact bodyRelated)
      (by rw [currentEq]; exact generated_block_statements_extended extended)
  rw [currentEq] at bodyPost bodyBounded
  have wholeBodyPost := enteredPost.comp bodyPost
  let valid := GeneratedClearBlockDemand source map required cx results before loop frame
  have bodyMapped : DemandUniformTraversal cx valid (block.stmts.length * 2)
      ⟨enteredPoint, enteredFrame, enteredState⟩ ⟨bodyEndPoint, bodyEndFrame, addressedState⟩ :=
    bodyTrace.mono (fun reached demanded => .body bodyCanonical demanded)
  exact ⟨body, bodyCanonical, bodyOccurrence, bodyRows, bodyAdmitted, bodyEndPoint, bodyEndFrame,
    .next (.entry enterSite coverage entryDemand)
      (fun fuel => .effect enterSite.instruction enterRun) bodyMapped,
    wholeBodyPost, bodyBounded, bodyRealized⟩

theorem accepted_generated_global_clear_block_traversal {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : GlobalClearStatements block.stmts)
    (noValue : block.value = none) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    {loop : Option LoopCtx}
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
      execBlock (fuel + 1) cfg env [] block state = .ok (.normal .unit) after ∧
      Post cfg env cx before frame (lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).2
        finalFrame finalPoint [((lowerBlock loop [] true block (lowerEnv cfg.mod env.vars results) before).1, .val .unit)] ∧
      map.Realizes cfg.mod source.world env ⟨finalPoint, finalFrame, after⟩ ∧
      (∀ taken actualFuel reached, taken ≤ block.stmts.length * 2 + 3 →
        DemandPrefix cx taken actualFuel ⟨point, frame, state⟩ reached →
        GeneratedClearBlockDemand source map required cx results before loop frame reached) ∧
      ∀ taken reached, taken ≤ block.stmts.length * 2 + 3 →
        DemandRuntimePrefix cx taken ⟨point, frame, state⟩ reached →
        GeneratedClearBlockDemand source map required cx results before loop frame reached := by
  let le := lowerEnv cfg.mod env.vars results
  let innerEnv : Env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }
  obtain ⟨body, bodyCanonical, bodyOccurrence, bodyRows, bodyAdmitted, bodyEndPoint, bodyEndFrame,
    prefixTrace, wholeBodyPost, bodyBounded, bodyRealized⟩ :=
    accepted_generated_global_clear_block_prefix source fragment occurrence rows coverage admitted bounded realized
      atPoint related extended statements
  have unitSite : GeneratedBlockUnitInstruction cfg.mod body.rootsEnv.access cx.fn required
      ⟨body.path, .block, .exit⟩ bodyEndPoint
      (.def (emitDef .constUnit le (demandBlockValueBefore le before loop [] block)).1 .constUnit) :=
    .unit bodyOccurrence bodyRows noValue wholeBodyPost.pp extended
  let unitRun := emitDef .constUnit le (demandBlockValueBefore le before loop [] block)
  let unitFrame := bodyEndFrame.set unitRun.1 (.val .unit)
  let unitPoint : Pt := (bodyEndPoint.1, bodyEndPoint.2 + 1)
  have unitExecuted : execOp 0 cx bodyEndFrame .constUnit addressedState = .ok (.val .unit) addressedState := by
    simp only [execOp, execPure, pure_apply]
  have unitStep : Evidence.RuntimeStep cx.cfg cx.fn bodyEndPoint bodyEndFrame addressedState unitPoint unitFrame addressedState :=
    .define unitSite.instruction unitExecuted
  obtain ⟨_, _, _, beforeUnitDemand, _, _, unitPost, unitDemand⟩ :=
    accepted_generated_block_unit_runtime_step body statements bodyOccurrence bodyCanonical.all bodyCanonical.scope bodyCanonical.value noValue
      bodyRows coverage wholeBodyPost bodyBounded bodyRealized extended unitStep
  have leaveSite := GeneratedDemandInstruction.blockLeave_auto occurrence rows unitPost.pp extended
  have leaveLabel : (match block.value with
      | some _ => (⟨source.path ++ [block.stmts.length], .expression, .exit⟩ : DemandSourceLabel)
      | none => ⟨source.path, .block, .exit⟩) = ⟨source.path, .block, .exit⟩ := by rw [noValue]
  let finalState : St := { addressedState with store := releaseVars env.vars env.act block.scope state.nextScope env.vars.size addressedState.store }
  let finalFrame : GIR.Frame := { unitFrame with scopes := env.scopes }
  let finalPoint : Pt := (unitPoint.1, unitPoint.2 + 1)
  have leaveRun : execEff cx.fn unitFrame (.leave block.scope) addressedState = .ok finalFrame finalState :=
    block_leave_exec (env := env) (scope := block.scope) (instanceId := state.nextScope) unitPost.rel addressedState
  have leaveStep : Evidence.RuntimeStep cx.cfg cx.fn unitPoint unitFrame addressedState finalPoint finalFrame finalState :=
    .effect leaveSite.instruction leaveRun
  obtain ⟨_, _, _, _, evaluatedBlock, finalPost, _, _, finalDemand⟩ :=
    accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized statements
      (show valueFlow fuel cfg block.value innerEnv (.normal .unit) addressedState = .ok (.normal .unit) addressedState from by
        rw [noValue]; rfl) unitPost extended leaveStep
  let valid := GeneratedClearBlockDemand source map required cx results before loop frame
  have beforeLeave : valid ⟨unitPoint, unitFrame, addressedState⟩ :=
    .leave bodyCanonical (leaveLabel ▸ leaveSite) coverage unitDemand
  have ending : DemandUniformTraversal cx valid 2 ⟨bodyEndPoint, bodyEndFrame, addressedState⟩
      ⟨finalPoint, finalFrame, finalState⟩ :=
    .next (.unitEntry bodyCanonical unitSite coverage beforeUnitDemand) (fun fuel => .definition unitSite.instruction (by simp only [execOp, execPure, pure_apply]))
      (.next beforeLeave (fun fuel => .effect leaveSite.instruction leaveRun)
        (.done (.exit finalPost (source.result (fuel + 1) (.normal .unit) evaluatedBlock) coverage finalDemand)))
  have assembled := prefixTrace.append ending
  have traversal : DemandUniformTraversal cx valid (block.stmts.length * 2 + 3)
      ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, finalState⟩ := by
    simpa only [Nat.add_assoc] using assembled
  refine ⟨finalState, finalPoint, finalFrame, traversal, evaluatedBlock, ?_, finalDemand.operands,
    fun taken actualFuel reached bound tracePrefix => traversal.prefix_invariant bound tracePrefix,
    fun taken reached bound steps => traversal.runtimePrefix_invariant bound steps⟩
  change Post cfg env cx before frame (lowerBlock loop [] true block le before).2 _ _
    [((lowerBlock loop [] true block le before).1, .val .unit)]
  rw [generated_block_value_result]
  exact finalPost

end Goose.Lower
