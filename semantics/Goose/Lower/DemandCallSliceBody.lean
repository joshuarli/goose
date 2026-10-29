import Goose.Lower.DemandCallPostPrologue
import Goose.Lower.DemandSliceAssignmentSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_slice_body_canonical {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (fragment : SliceAssignmentStatements block.stmts)
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
            (@SliceAssignmentCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results)
            taken reached ∧
          RuntimePoint cx.cfg cx.fn (start.1, start.2 + 1 + bindings.length)
            { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
            { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
  obtain ⟨body, bodyAll, bodyScope, bodyValue, bodyOffset, bodyCanonical, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted,
    bodyBounded, bodyRealized, bodyInput, prologuePost, bodyReached⟩ :=
    accepted_generated_post_prologue_canonical source selected owned occurrence rows coverage admitted bounded cells realized input extended entry
  have family : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before none bindings want block block.stmts
      (@SliceAssignmentCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results) :=
    accepted_generated_slice_assignment_sequence_prefix
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected before none bindings want block fragment
  have bodyBounded' : map.Bounded (lowerStmts none (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.vals.size := by
    simpa [bodyOffset, lowerStmts, pure_run] using bodyBounded
  have statementsExtended : ExtT (lowerStmts none block.stmts (lowerEnv cfg.mod env.vars results)
      (lowerStmts none (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2).2 cx.fn.blocks := by
    simpa [bodyOffset, lowerStmts, pure_run] using generated_block_statements_extended extended
  have normalizedInput := bodyInput
  simp only [bodyOffset, List.take_zero, lowerStmts, pure_run] at normalizedInput
  exact ⟨body, bodyOffset, bodyCanonical, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted, bodyBounded, bodyRealized, normalizedInput, prologuePost,
    family body bodyOwned bodyOccurrence bodyAll bodyScope bodyValue bodyRows coverage bodyAdmitted bodyBounded'
      bodyRealized bodyInput statementsExtended steps, bodyReached⟩


#print axioms accepted_generated_parameterized_slice_body_canonical
end Goose.Lower
