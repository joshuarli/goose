import Goose.Lower.DemandIntegerAssignmentStatementsNormal
import Goose.Lower.DemandControlBlockPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive GeneratedIntegerAssignmentBlockPrefixDemand {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (map required : RetainedSsaMap) (before : LS) (loop : Option LoopCtx) (initial : GIR.Frame)
    (suffixCursor : DemandRuntimePoint → Prop) : DemandRuntimePoint → Prop
  | emitted {runtime : DemandRuntimePoint}
      (demanded : GeneratedClearBlockDemand source map required cx results before loop initial runtime) :
      GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial suffixCursor runtime
  | suffix {runtime : DemandRuntimePoint} (demanded : suffixCursor runtime) :
      GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial suffixCursor runtime
  | body {body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        block.stmts { state with nextScope := state.nextScope + 1 }} {start : Pt} {runtime : DemandRuntimePoint}
      (canonical : GeneratedBlockBodyAt source body)
      (demanded : GeneratedSequencePrefixCursor
        (@IntegerAssignmentStatementPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results)
        map required cx results before loop [] block selected body
        ⟨start, { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
          { state with nextScope := state.nextScope + 1 }⟩ runtime) :
      GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial suffixCursor runtime

theorem accepted_generated_integer_assignment_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : IntegerAssignmentStatements block.stmts)
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
      (GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial suffixCursor) taken reached := by
  refine ⟨owned, coverage, ?_⟩
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] true block block.stmts
      (@IntegerAssignmentStatementPrefixCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) :=
    (accepted_generated_integer_assignment_statements_agreement (cfg := cfg)
    (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) (cx := cx) (results := results)
    selected before loop [] true block fragment).1
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

theorem accepted_generated_integer_assignment_unit_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) (fragment : IntegerAssignmentStatements block.stmts)
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
      (GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial
        (GeneratedClearBlockDemand source map required cx results before loop initial)) taken reached := by
  apply accepted_generated_integer_assignment_block_prefix source fragment selected owned occurrence rows coverage admitted bounded
    realized input extended (GeneratedClearBlockDemand source map required cx results before loop initial) ?_ steps
  intro body canonical bodyOccurrence bodyRows bodyInput fuel addressed statements post bodyBounded bodyRealized consumed taken reached prefixSteps residual
  exact accepted_generated_block_unit_suffix_prefix source body canonical noValue occurrence bodyOccurrence rows bodyRows
    coverage admitted bounded realized statements post bodyBounded bodyRealized extended prefixSteps residual


theorem IntegerAssignmentPrefixCursor.frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : IntegerAssignmentPrefixCursor cx results source before built initial start map required runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  have carried := cursor.realizes
  cases cursor with
  | destination child canonical demanded =>
    exact ⟨_, _, _, ⟨demanded.builder, by simpa only [canonical.world] using demanded.source, carried⟩⟩
  | value child canonical aliases demanded =>
    obtain ⟨typing, roots, future, frame⟩ := demanded.frame
    exact ⟨typing, roots, future, ⟨frame.builder, by simpa only [canonical.world] using frame.source, carried⟩⟩
  | store child canonical aliases site demanded =>
    exact ⟨_, _, _, ⟨demanded.builder, by simpa only [canonical.world] using demanded.source, carried⟩⟩

theorem IntegerAssignmentStatementPrefixCursor.frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : IntegerAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  cases cursor with
  | control cursor => exact cursor.frame
  | assignment cursor => exact cursor.frame

theorem GeneratedSequencePrefixCursor.integer_assignment_frame {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@IntegerAssignmentStatementPrefixCursor cfg env cx results)
      map required cx results before loop bindings block selected source initial runtime) :
    ∃ typing roots future, DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime := by
  induction cursor with
  | head canonical owned occurrence rows coverage demanded =>
    simpa only [canonical.world] using demanded.frame
  | tail canonical evaluated prefixSteps post demanded ih =>
    simpa only [canonical.world] using ih

theorem GeneratedIntegerAssignmentBlockPrefixDemand.frame {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    {suffixCursor : DemandRuntimePoint → Prop}
    (suffixFrame : ∀ runtime, suffixCursor runtime → ∃ typing roots future,
      DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime ∨
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx source.world typing roots future map.values map.runs runtime)
    (demanded : GeneratedIntegerAssignmentBlockPrefixDemand source selected map required before loop initial suffixCursor runtime) :
    ∃ typing roots future,
      DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime ∨
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        cx source.world typing roots future map.values map.runs runtime := by
  cases demanded with
  | emitted demanded => exact demanded.frame
  | suffix demanded => exact suffixFrame _ demanded
  | body canonical demanded =>
    obtain ⟨typing, roots, future, framed⟩ := demanded.integer_assignment_frame
    exact ⟨typing, roots, future, Or.inr (by simpa only [canonical.world] using framed)⟩

#print axioms GeneratedIntegerAssignmentBlockPrefixDemand.frame
#print axioms accepted_generated_integer_assignment_block_prefix
#print axioms accepted_generated_integer_assignment_unit_block_prefix

end Goose.Lower
