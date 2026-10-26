import Goose.Lower.DemandGeneratedParameterStep
import Goose.Lower.DemandGeneratedTransfer

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_body_entry {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (cells : PreRel frame bindings pre)
    {initialPoint : Pt} (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, frame, state⟩)
    {point : Pt} (atPoint : (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).pp = some point)
    (related : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)) :
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      body.typingEnv = source.typingInner ∧ body.typingAfter = source.typingAfter ∧
      body.rootsEnv = { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes } ∧
      body.world = source.world ∧ body.observation = source.observation ∧
      body.typingStart = source.typingStart ∧ body.typingEnd = source.typingValue ∧
      body.rootsStart = source.rootsStart ∧ body.rootsEnd = source.rootsValue ∧
      body.plans = source.plans ∧ body.path = source.path ∧ body.scope = block.scope ∧
      body.all = block.stmts ∧ body.value = block.value ∧ body.offset = 0 ∧ HEq body.context source.context ∧
    ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
        root body.path (.block loop bindings want block) before,
      GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required ∧ map.Covers required ∧
      map.Admitted cfg.mod.profile body.context.retained ∧
      PreRel { frame with scopes := (block.scope, state.nextScope) :: frame.scopes } bindings pre ∧
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx body.world
        body.typingEnv body.rootsEnv (blockSuffixFuture body.context body.offset) map.values map.runs
        ⟨point, { frame with scopes := (block.scope, state.nextScope) :: frame.scopes },
          { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ := by
  obtain ⟨body, typing, finalTyping, roots, world, observation, typingStart, typingEnd,
    rootsStart, rootsEnd, plans, path, context, all, value, offset, scope⟩ := source.enter
  obtain ⟨cursor⟩ := source.parameterPrefix pre.length
  have carried := cursor.retained_inner realized
  have bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root body.path (.block loop bindings want block) before := by
    rw [path]
    exact occurrence
  have bodyRows : GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required := by
    simpa only [roots, path, PEnv.access] using rows
  have bodyNode : DemandNode.block (.mk body.scope body.all body.value) = .block block := by
    rw [scope, all, value]
    cases block
    rfl
  have retainedEq := demandContextRetainedEq plans path bodyNode context
  have bodyAdmitted : map.Admitted cfg.mod.profile body.context.retained := by
    simpa only [retainedEq] using admitted
  refine ⟨body, typing, finalTyping, roots, world, observation, typingStart, typingEnd,
    rootsStart, rootsEnd, plans, path, scope, all, value, offset, context, bodyOccurrence, bodyRows, coverage,
    bodyAdmitted, PreRel.ext (fr := frame) (fr' := { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }) rfl cells, ⟨⟨_, atPoint, related⟩, body.frame, ?_⟩⟩
  simpa only [RetainedSsaMap.Realizes, world, List.take_length] using carried

theorem generated_statement_prefix_next {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {offset : Nat} {stmt : Stmt} {point : Pt}
    (selected : block.stmts[offset]? = some stmt)
    (atPoint : (lowerStmts loop (block.stmts.take offset) le
      (demandBlockStatementsBefore le before bindings block)).2.pp = some point) :
    (lowerStmts loop (block.stmts.take (offset + 1)) le
      (demandBlockStatementsBefore le before bindings block)).2 =
      (lowerStmt loop stmt le (lowerStmts loop (block.stmts.take offset) le
        (demandBlockStatementsBefore le before bindings block)).2).2 := by
  obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp selected
  obtain ⟨currentBlock, current, _, _⟩ := LS.pp_some atPoint
  rw [List.take_succ_eq_append_getElem bound, found, lowerStmts_append_run]
  simp only [lowerStmts, bind_run, isLive_run current, ite_true, pure_run]

theorem accepted_generated_statement_entry {cfg : Cfg} {env : Env} {stmt : Stmt} {rest : List Stmt}
    {state : St} (source : StmtsSource cfg env (stmt :: rest) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    (all : source.all = block.stmts) (scope : source.scope = block.scope) (value : source.value = block.value)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} {point : Pt}
    (atPoint : (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2.pp = some point)
    (related : Rel cfg env cx frame (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩) :
    ∃ head : StmtSource cfg env stmt state, source.CanonicalHead head ∧
      DemandNode.block (.mk source.scope source.all source.value) = .block block ∧
      head.typingEnv = source.typingEnv ∧ head.rootsEnv = source.rootsEnv ∧
    ∃ headOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root head.path
        (.statement loop stmt) (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2,
      GeneratedDemandRows cfg.mod head.rootsEnv.access headOccurrence required ∧ map.Covers required ∧
      map.Admitted cfg.mod.profile head.context.retained ∧
      DemandFrameAt cfg env cx head.world head.typingEnv head.rootsEnv head.context.inputFuture
        map.values map.runs ⟨point, frame, state⟩ ∧
      ∀ fuel runtimeValue after, execStmt fuel cfg env stmt state = .ok (.normal runtimeValue) after →
        ∃ tail : StmtsSource cfg env rest after, tail.typingEnv = head.typingAfter ∧
          tail.rootsEnv = source.rootsEnv ∧ tail.typingAfter = source.typingAfter ∧ source.CanonicalTail tail := by
  obtain ⟨head, typing, roots, canonical, next⟩ := source.splitDemand
  have selected : block.stmts[source.offset]? = some stmt := by
    have suffix : stmt :: rest = block.stmts.drop source.offset := by simpa only [all] using source.suffix
    have first : (block.stmts.drop source.offset)[0]? = some stmt := by rw [← suffix]; rfl
    simpa only [List.getElem?_drop, Nat.add_zero] using first
  have headOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root head.path
      (.statement loop stmt) (lowerStmts loop (block.stmts.take source.offset) (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 := by
    rw [canonical.path]
    exact .blockStatement occurrence selected
  have headRows : GeneratedDemandRows cfg.mod head.rootsEnv.access headOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.blockStatement occurrence selected) required := .blockStatement (statementAt := selected) rows
    simpa only [roots, canonical.path] using inherited
  have headRealized : map.Realizes cfg.mod head.world env ⟨point, frame, state⟩ := by
    simpa only [canonical.world] using realized
  have blockEq : DemandNode.block (.mk source.scope source.all source.value) = .block block := by
    rw [scope, all, value]
    cases block
    rfl
  refine ⟨head, canonical, blockEq, typing, roots, headOccurrence, headRows, coverage, ?_,
    ⟨⟨_, atPoint, related⟩, head.frame, headRealized⟩, next⟩
  intro shrink alias member
  exact canonical.retained alias (admitted shrink alias member)

end Goose.Lower
