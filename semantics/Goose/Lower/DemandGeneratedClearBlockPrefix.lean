import Goose.Lower.DemandGeneratedBlockSuffixPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedClearBlockPrefixDemand {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame)
    (suffixCursor : DemandRuntimePoint → Prop) : DemandRuntimePoint → Prop
  | emitted {runtime : DemandRuntimePoint}
      (demanded : GeneratedClearBlockDemand source map required cx results before loop initial runtime) :
      GeneratedClearBlockPrefixDemand source selected map required before loop initial suffixCursor runtime
  | suffix {runtime : DemandRuntimePoint} (demanded : suffixCursor runtime) :
      GeneratedClearBlockPrefixDemand source selected map required before loop initial suffixCursor runtime
  | body {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }} {start : Pt} {runtime : DemandRuntimePoint}
      (canonical : GeneratedBlockBodyAt source body)
      (demanded : GeneratedSequencePrefixCursor
        (@GeneratedGlobalClearPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results)
        map required cx results before loop [] block selected body
        ⟨start, { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
          { state with nextScope := state.nextScope + 1 }⟩ runtime) :
      GeneratedClearBlockPrefixDemand source selected map required before loop initial suffixCursor runtime

theorem accepted_generated_clear_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : GlobalClearStatements block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS} {loop : Option LoopCtx}
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
    (suffixCursor : DemandRuntimePoint → Prop)
    (suffixFamily : GeneratedBlockSuffixPrefixFamily source selected map required before loop initial start suffixCursor)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedBlockPrefixDecomposition source selected map required before loop initial start
      (GeneratedClearBlockPrefixDemand source selected map required before loop initial suffixCursor) taken reached := by
  refine ⟨owned, coverage, ?_⟩
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] true block block.stmts
      (@GeneratedGlobalClearPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) :=
    accepted_generated_global_clears_prefix (cfg := cfg)
    (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) (cx := cx) (results := results)
    selected before loop [] true block fragment
  have progress := accepted_generated_block_statements_prefix source selected owned occurrence rows coverage admitted bounded
    realized input extended _ bodyFamily steps
  rcases progress with ⟨_, _, entry⟩ | progressed
  · exact .interior (.emitted entry)
  · cases progressed with
    | intro body canonical bodyOccurrence bodyRows remaining count enterStep _bodyInput bodyProgress =>
      cases bodyProgress.progress with
      | interior demanded => exact .interior (.body canonical demanded)
      | @complete sourceFuel consumed residualLength boundary flow bodyCount bodySteps residual evaluated finished =>
        cases finished with
        | transfer abnormal post =>
          simp only [bind_apply] at evaluated
          cases raw : execStmts sourceFuel cfg
              { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
              { state with nextScope := state.nextScope + 1 } with
          | stop stop final => simp only [raw] at evaluated; cases evaluated
          | ok rawFlow rawState =>
            have normal := fragment.normal raw
            subst rawFlow
            simp only [raw] at evaluated
            have prepared : prepareLoopFlow { env with scopes := (block.scope, state.nextScope) :: env.scopes }
                loop (.normal .unit) rawState = .ok (.normal .unit) rawState := by cases loop <;> rfl
            rw [prepared] at evaluated
            exact (abnormal .unit (Res.ok.inj evaluated).1.symm).elim
        | normal bodyPost bodyResult bodyBounded bodyRealized =>
          have raw := preparedLoopFlow_normal_success evaluated
          have currentEq : (lowerStmts loop (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)).2 =
              demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block := by
            simp only [canonical.offset, List.take_zero, lowerStmts, pure_run]
          rw [currentEq] at bodyPost bodyBounded
          have enteredValues : (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block).vals.size = before.vals.size := by
            have values := (emitEffect_facts (show emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before =
              ((emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before).1,
               (emitEffect (.enter block.scope) (lowerEnv cfg.mod env.vars results) before).2) from rfl)
              input.atPoint (generated_block_enter_extended extended)).1
            simpa only [demandBlockStatementsBefore, initSlots, pure_run] using values
          obtain ⟨_, _, _, _, _, _, _, enterPoint, enterRelated, _, _⟩ :=
            accepted_generated_block_enter_runtime_step source occurrence rows coverage bounded input.atPoint input.related realized extended enterStep
          have enteredPost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
              (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before [] block)
              { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1) [] :=
            ⟨enterPoint, by simp, by simp, Nat.le_of_eq enteredValues.symm, fun _ _ => rfl, enterRelated⟩
          have suffix := suffixFamily body canonical bodyOccurrence bodyRows _bodyInput _ _ raw
            (enteredPost.comp bodyPost) bodyBounded bodyRealized _ _ _ (DemandRuntimePrefix.next enterStep bodySteps) residual
          cases suffix with
          | interior demanded => exact .interior (.suffix demanded)
          | complete suffixCount prefixSteps residual evaluated post =>
            exact .complete (by omega) prefixSteps residual evaluated post

theorem accepted_generated_clear_unit_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : GlobalClearStatements block.stmts)
    (noValue : block.value = none) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {before : LS} {loop : Option LoopCtx}
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
      (GeneratedClearBlockPrefixDemand source selected map required before loop initial
        (GeneratedClearBlockDemand source map required cx results before loop initial)) taken reached := by
  apply accepted_generated_clear_block_prefix source fragment selected owned occurrence rows coverage admitted bounded
    realized input extended (GeneratedClearBlockDemand source map required cx results before loop initial) ?_ steps
  intro body canonical bodyOccurrence bodyRows bodyInput fuel addressed statements post bodyBounded bodyRealized consumed taken reached prefixSteps residual
  exact accepted_generated_block_unit_suffix_prefix source body canonical noValue occurrence bodyOccurrence rows bodyRows
    coverage admitted bounded realized statements post bodyBounded bodyRealized extended prefixSteps residual

theorem GeneratedClearBlockPrefixDemand.frame {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    {suffixCursor : DemandRuntimePoint → Prop}
    (suffixFrame : ∀ runtime, suffixCursor runtime → ∃ typing roots future,
      DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime ∨
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx source.world typing roots future map.values map.runs runtime)
    (demanded : GeneratedClearBlockPrefixDemand source selected map required before loop initial suffixCursor runtime) :
    ∃ typing roots future,
      DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime ∨
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx source.world typing roots future map.values map.runs runtime := by
  cases demanded with
  | emitted demanded => exact demanded.frame
  | suffix demanded => exact suffixFrame _ demanded
  | body canonical demanded =>
    obtain ⟨typing, roots, future, framed⟩ := demanded.globalClear_frame
    exact ⟨typing, roots, future, Or.inr (by simpa only [canonical.world] using framed)⟩

end Goose.Lower
