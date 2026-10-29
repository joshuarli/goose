import Goose.Lower.DemandCallParameterizedSequence
import Goose.Lower.DemandCallSliceBody
import Goose.Lower.DemandCallSliceMixedSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_slice_mixed_body_canonical {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (fragment : SliceMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (cells : PreRel initial bindings pre)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (entry : RuntimePoint cx.cfg cx.fn start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken
      ⟨(start.1, start.2 + 1 + bindings.length), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ reached) :
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      body.offset = 0 ∧ ParameterizedBlockBodyAt source body ∧ ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root body.path (.block none bindings want block) before,
        ∃ bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required,
          GeneratedSourceOwner selected body.context ∧ map.Admitted cfg.mod.profile body.context.retained ∧
          map.Bounded (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).vals.size ∧
          map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
            ⟨(start.1, start.2 + 1 + bindings.length), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
              { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ ∧
          GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results none
            body.typingEnv body.rootsEnv (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) ∧
          Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) [] ∧
          GeneratedSequencePrefixDecomposition body selected bodyOccurrence bodyRows map
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
            (start.1, start.2 + 1 + bindings.length)
            (@SliceMixedCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results root owner selected)
            taken reached ∧
          RuntimePoint cx.cfg cx.fn (start.1, start.2 + 1 + bindings.length)
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
            { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
  exact accepted_generated_parameterized_body_family_canonical source selected owned occurrence rows coverage admitted bounded
    cells realized input extended entry _ (accepted_generated_slice_mixed_statements fragment selected before bindings want block).1 steps


theorem accepted_generated_parameterized_slice_mixed_body_stopped_canonical {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (fragment : SliceMixedStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (cells : PreRel initial bindings pre)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (entry : RuntimePoint cx.cfg cx.fn start initial state)
    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken
      ⟨(start.1, start.2 + 1 + bindings.length), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      body.offset = 0 ∧ ParameterizedBlockBodyAt source body ∧
      ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root body.path (.block none bindings want block) before,
      GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required ∧
      GeneratedSourceOwner selected body.context ∧ map.Admitted cfg.mod.profile body.context.retained ∧
      map.Bounded (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).vals.size ∧
      map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
        ⟨(start.1, start.2 + 1 + bindings.length), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ ∧
      GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results none
        body.typingEnv body.rootsEnv (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) ∧
      Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) [] ∧
      StoppedSequencePrefix body map cx results before none bindings block
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
        (start.1, start.2 + 1 + bindings.length) taken reached stop after ∧
      RuntimePoint cx.cfg cx.fn (start.1, start.2 + 1 + bindings.length)
        { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
  exact accepted_generated_parameterized_body_stopped_family_canonical source selected owned occurrence rows coverage admitted bounded
    cells realized input extended entry (accepted_generated_slice_mixed_statements fragment selected before bindings want block).2 steps stopped nonTimeout

#print axioms accepted_generated_parameterized_slice_mixed_body_canonical
#print axioms accepted_generated_parameterized_slice_mixed_body_stopped_canonical
end Goose.Lower
