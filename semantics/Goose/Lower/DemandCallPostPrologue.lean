import Goose.Lower.DemandCallPrologueLayout
import Goose.Lower.DemandWhileMixedStatements

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_post_prologue {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
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
    (reached : RuntimePoint cx.cfg cx.fn start initial state) :
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      body.all = block.stmts ∧ body.scope = block.scope ∧ body.value = block.value ∧ body.offset = 0 ∧
      ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root body.path (.block none bindings want block) before,
        GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required ∧
        GeneratedSourceOwner selected body.context ∧ map.Admitted cfg.mod.profile body.context.retained ∧
        map.Bounded (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).vals.size ∧
        map.Realizes cfg.mod body.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
          ⟨(start.1, start.2 + 1 + bindings.length), { initial with scopes := (block.scope, state.nextScope) :: initial.scopes },
            { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ ∧
        GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx results none
          body.typingEnv body.rootsEnv
          (lowerStmts none (block.stmts.take body.offset) (lowerEnv cfg.mod env.vars results)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2
          { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) ∧
        Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
          { initial with scopes := (block.scope, state.nextScope) :: initial.scopes } (start.1, start.2 + 1 + bindings.length) [] ∧
        RuntimePoint cx.cfg cx.fn (start.1, start.2 + 1 + bindings.length)
          { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
  let le := lowerEnv cfg.mod env.vars results
  let raw := (emitEffect (.enter block.scope) le before).2
  let entered := { raw with stack := block.scope :: raw.stack }
  let bodyBefore := demandBlockStatementsBefore le before bindings block
  let innerFrame : GIR.Frame := { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
  let bodyPoint : Pt := (start.1, start.2 + 1 + bindings.length)
  have slotsExtended : ExtT (initSlots bindings le entered).2 cx.fn.blocks := by
    simpa [bodyBefore, demandBlockStatementsBefore, entered, raw] using generated_block_parameters_extended extended
  have rawExtended : ExtT raw cx.fn.blocks := generated_block_enter_extended extended
  obtain ⟨rawValues, rawStack, rawPoint, _⟩ := emitEffect_facts
    (show emitEffect (.enter block.scope) le before =
      ((emitEffect (.enter block.scope) le before).1, raw) from rfl) input.atPoint rawExtended
  have enteredPoint : entered.pp = some (start.1, start.2 + 1) := by simpa [entered, LS.pp] using rawPoint
  have enteredValues : entered.vals.size = before.vals.size := by simpa [entered] using rawValues
  have enteredStack : entered.stack = block.scope :: before.stack := by simp [entered, rawStack]
  obtain ⟨slotsPoint, slotsValues, slotsStack⟩ := initSlots_layout bindings enteredPoint slotsExtended
  have bodyEq : bodyBefore = (initSlots bindings le entered).2 := by
    simp [bodyBefore, demandBlockStatementsBefore, entered, raw]
  have bodyAt : bodyBefore.pp = some bodyPoint := by
    rw [bodyEq]
    simpa [bodyPoint, Nat.add_assoc] using slotsPoint
  have bodyValues : bodyBefore.vals.size = before.vals.size := by
    rw [bodyEq]
    exact slotsValues.trans enteredValues
  have bodyStack : bodyBefore.stack = block.scope :: before.stack := by
    rw [bodyEq]
    exact slotsStack.trans enteredStack
  have bodyRelated : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx innerFrame bodyBefore :=
    ⟨input.related.prof, input.related.slots, input.related.act, by simp [innerFrame, input.related.scopes], input.related.depth,
      by rw [bodyStack, input.related.stack]; rfl⟩
  obtain ⟨body, bodyTyping, bodyTypingAfter, bodyRoots, bodyWorld, bodyObservation, bodyTypingStart, bodyTypingEnd,
    bodyRootsStart, bodyRootsEnd, bodyPlans, bodyPath, bodyScope, bodyAll, bodyValue, bodyOffset, bodyContext,
    bodyOccurrence, bodyRows, _, bodyAdmitted, _, bodyDemand⟩ :=
    accepted_generated_body_entry source occurrence rows coverage admitted cells realized bodyAt bodyRelated
  have bodyOwned : GeneratedSourceOwner selected body.context :=
    owned.transport bodyPlans.symm bodyPath.symm (by rw [bodyScope, bodyAll, bodyValue]; cases block; rfl) bodyContext.symm
  have currentEq : (lowerStmts none (block.stmts.take body.offset) le bodyBefore).2 = bodyBefore := by
    simp [bodyOffset, lowerStmts, pure_run]
  have generatedEntered := input.generated.emitEffect (.enter block.scope)
    (show emitEffect (.enter block.scope) le before =
      ((emitEffect (.enter block.scope) le before).1, raw) from rfl)
  have generatedBody : GeneratedBuilderState bodyBefore := by
    rw [bodyEq]
    exact (show GeneratedBuilderState entered from ⟨generatedEntered.dense, generatedEntered.live, generatedEntered.targets⟩).initSlots bindings rfl
  have bodyInput : GeneratedPrefixInput cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      cx results none body.typingEnv body.rootsEnv (lowerStmts none (block.stmts.take body.offset) le bodyBefore).2 innerFrame bodyPoint := by
    rw [currentEq]
    refine ⟨?_, ?_, bodyAt, bodyRelated, input.moduleEq, input.resultsEq,
      loopDepthFits_entered block.scope state.nextScope input.depth, trivial,
      input.counter.sameValues rfl bodyValues, generatedBody, trivial⟩
    apply input.metadata.transport
    · rw [bodyTyping]; exact source.same.impl
    · rw [bodyRoots]
    · apply input.loops.transport
      rw [bodyTyping]; exact source.same.loops
  have lowered : lowerBlock none bindings want block le before =
      ((lowerBlock none bindings want block le before).1, (lowerBlock none bindings want block le before).2) := rfl
  have prologue := accepted_block_parameter_prologue source lowered input.atPoint extended input.related cells reached pre.length (by omega)
  have reachable : RuntimePoint cx.cfg cx.fn bodyPoint innerFrame
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
    simpa [bodyPoint, innerFrame, cells.length] using prologue.2.1
  have prologuePost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      bodyBefore innerFrame bodyPoint [] := by
    refine ⟨bodyAt, by simp, by simp, ?_, ?_, bodyRelated⟩
    · rw [bodyValues]; exact Nat.le_refl _
    · intro id bound
      rfl
  refine ⟨body, bodyAll, bodyScope, bodyValue, bodyOffset, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted, ?_, ?_, bodyInput, prologuePost, reachable⟩
  · rw [bodyValues]; exact bounded
  · exact bodyDemand.operands

#print axioms accepted_generated_post_prologue
end Goose.Lower
