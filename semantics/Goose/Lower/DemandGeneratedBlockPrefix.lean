import Goose.Lower.DemandGeneratedGlobalClearPrefix
import Goose.Lower.DemandGeneratedClearBlock

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedBlockStatementsPrefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (initial : GIR.Frame) (start : Pt)
    (cursor : ∀ {statement : Stmt} {innerState : St},
      StmtSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (taken : Nat) (reached : DemandRuntimePoint) : Prop
  | intro (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      block.stmts { state with nextScope := state.nextScope + 1 })
      (canonical : GeneratedBlockBodyAt source body)
      (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root body.path (.block loop [] true block) before)
      (rows : GeneratedDemandRows cfg.mod body.rootsEnv.access occurrence required)
      (remaining : Nat) (count : remaining + 1 = taken)
      (entry : Evidence.RuntimeStep cx.cfg cx.fn start initial state
        (start.1, start.2 + 1) { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
        { state with nextScope := state.nextScope + 1 })
      (input : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx results loop body.typingEnv body.rootsEnv
        (lowerStmts loop (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)).2
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1))
      (progress : GeneratedSequencePrefixDecomposition (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
        body selected occurrence rows map
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1)
        (@cursor) remaining reached) :
      GeneratedBlockStatementsPrefix (before := before) (loop := loop) source selected map required initial start (@cursor) taken reached

theorem accepted_generated_block_statements_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
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
    (cursor : ∀ {statement : Stmt} {innerState : St},
      StmtSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before loop [] true block block.stmts (@cursor))
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    (taken = 0 ∧ reached = ⟨start, initial, state⟩ ∧
      GeneratedClearBlockDemand source map required cx results before loop initial reached) ∨
      GeneratedBlockStatementsPrefix (before := before) (loop := loop) source selected map required initial start (@cursor) taken reached := by
  let le := lowerEnv cfg.mod env.vars results
  let enteredFrame : GIR.Frame := { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
  let enteredState : St := { state with nextScope := state.nextScope + 1 }
  let enteredPoint : Pt := (start.1, start.2 + 1)
  let bodyBefore := demandBlockStatementsBefore le before [] block
  have enterSite := GeneratedDemandInstruction.blockEnter_auto occurrence rows input.atPoint extended
  have enterRun : execEff cx.fn initial (.enter block.scope) state = .ok enteredFrame enteredState := by
    simp only [execEff, freshScope, bind_apply, pure_apply, enteredFrame, enteredState]
  have enterStep : Evidence.RuntimeStep cx.cfg cx.fn start initial state enteredPoint enteredFrame enteredState :=
    .effect enterSite.instruction enterRun
  obtain ⟨_, entryDemand, _, _, _, _, _, bodyPoint, bodyRelated, _, _⟩ :=
    accepted_generated_block_enter_runtime_step source occurrence rows coverage bounded input.atPoint input.related realized extended enterStep
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, middle, count, first, residual⟩
  · exact Or.inl ⟨zero, rfl, .entry enterSite coverage entryDemand⟩
  · obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep first
    have expected : DemandInstructionStep cx fuel ⟨start, initial, state⟩ ⟨enteredPoint, enteredFrame, enteredState⟩ :=
      .effect enterSite.instruction enterRun
    have same := first.deterministic expected
    have middleEq : middle = ⟨enteredPoint, enteredFrame, enteredState⟩ :=
      (show middle = ⟨middle.point, middle.frame, middle.state⟩ from by cases middle; rfl).trans same
    subst middle
    obtain ⟨body, bodyTyping, bodyTypingAfter, bodyRoots, bodyWorld, _, _, bodyTypingEnd, _, bodyRootsEnd,
      bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext,
      bodyOccurrence, bodyRows, _, bodyAdmitted, _, bodyDemand⟩ :=
      accepted_generated_body_entry source occurrence rows coverage admitted (show PreRel initial [] [] from trivial)
        realized bodyPoint bodyRelated
    have canonical : GeneratedBlockBodyAt source body :=
      ⟨bodyWorld, bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext,
        bodyRoots, bodyTypingAfter, bodyTypingEnd, bodyRootsEnd⟩
    have bodyOwned : GeneratedSourceOwner selected body.context :=
      owned.transport bodyPlans.symm bodyPath.symm (by rw [bodyScope, bodyAll, bodyValue]; cases block; rfl) bodyContext.symm
    have currentEq : (lowerStmts loop (block.stmts.take body.offset) le bodyBefore).2 = bodyBefore := by
      simp only [bodyOffset, List.take_zero, lowerStmts, pure_run]
    have enteredValues : bodyBefore.vals.size = before.vals.size := by
      have values := (emitEffect_facts (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)
        input.atPoint (generated_block_enter_extended extended)).1
      simpa only [bodyBefore, demandBlockStatementsBefore, initSlots, pure_run] using values
    have generatedEntered := input.generated.emitEffect (.enter block.scope)
      (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)
    have bodyGenerated : GeneratedBuilderState bodyBefore :=
      ⟨generatedEntered.dense, generatedEntered.live, generatedEntered.targets⟩
    have bodyFrames : LoopBuilderFrames loop bodyBefore :=
      input.frames.mono (adv_emitEffect (show emitEffect (.enter block.scope) le before =
        ((emitEffect (.enter block.scope) le before).1, (emitEffect (.enter block.scope) le before).2) from rfl)).ext
    have bodyInput : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx results loop body.typingEnv body.rootsEnv
        (lowerStmts loop (block.stmts.take body.offset) le bodyBefore).2 enteredFrame enteredPoint := by
      rw [currentEq]
      refine ⟨?_, ?_, bodyPoint, bodyRelated, input.moduleEq, input.resultsEq,
        loopDepthFits_entered block.scope state.nextScope input.depth,
        (by cases loop <;> exact input.targets), input.counter.sameValues rfl enteredValues,
        bodyGenerated, bodyFrames⟩
      · apply input.metadata.transport
        · rw [bodyTyping]; exact source.same.impl
        · rw [bodyRoots]
      · apply input.loops.transport
        rw [bodyTyping]; exact source.same.loops
    have bodyProgress := bodyFamily body bodyOwned bodyOccurrence bodyAll bodyScope bodyValue bodyRows coverage bodyAdmitted
      (by rw [currentEq, enteredValues]; exact bounded) bodyDemand.operands bodyInput
      (by rw [currentEq]; exact generated_block_statements_extended extended) residual
    exact Or.inr ⟨body, canonical, bodyOccurrence, bodyRows, remaining, count.symm, enterStep, bodyInput, bodyProgress⟩

end Goose.Lower
