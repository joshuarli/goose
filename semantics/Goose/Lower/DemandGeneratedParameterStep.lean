import Goose.Lower.DemandGeneratedParameters

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def demandParameterState (env : Env) (state : St) (pre : List (VarId × Val)) (count : Nat) : St :=
  { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }

private theorem preStore_append (act : ActId) (instanceId : ScopeInst) (first rest : List (VarId × Val))
    (store : Store) : preStore act instanceId (first ++ rest) store =
      preStore act instanceId rest (preStore act instanceId first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons binding first induction =>
    rcases binding with ⟨slot, value⟩
    simpa only [List.cons_append, preStore] using induction (store.introduce (.local act instanceId slot) value)

private theorem parameterState_succ {env : Env} {state : St} {pre : List (VarId × Val)}
    {count : Nat} {slot : VarId} {value : Val} (selected : pre[count]? = some (slot, value)) :
    demandParameterState env state pre (count + 1) =
      { demandParameterState env state pre count with
        store := (demandParameterState env state pre count).store.introduce (.local env.act state.nextScope slot) value } := by
  obtain ⟨bound, row⟩ := List.getElem?_eq_some_iff.mp selected
  simp only [demandParameterState]
  rw [List.take_succ_eq_append_getElem bound, row, preStore_append]
  rfl

theorem accepted_generated_parameter_runtime_step {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state after : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {count : Nat} {slot : SlotId} {id : ValueId} {origin : OriginId}
    (bindingAt : bindings[count]? = some (slot, id, origin)) {frame : GIR.Frame}
    (cells : PreRel frame bindings pre)
    {initialPoint : Pt} (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, frame, state⟩)
    {point : Pt} (atPoint : (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block count).pp = some point)
    (related : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
      (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block count))
    (bounded : map.Bounded (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block count).vals.size)
    (extended : ExtT (lowerBlock loop bindings want block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point
      { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
      (demandParameterState env state pre count) next nextFrame after) :
    GeneratedBlockParameterInstruction cfg.mod source.rootsEnv.access cx.fn required ⟨source.path, .block, .entry⟩ point
      (.eff (.slotInit slot id (some origin))) ∧
    ∃ current : ParameterPrefixCursor source count, ∃ following : ParameterPrefixCursor source (count + 1),
      map.Covers required ∧
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx source.world
        current.typing { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
        ((pre.take count).map Prod.fst ++ source.context.inputFuture) map.values map.runs
        ⟨point, { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }, demandParameterState env state pre count⟩ ∧
      next = (point.1, point.2 + 1) ∧
      nextFrame = { frame with scopes := (block.scope, state.nextScope) :: frame.scopes } ∧
      after = demandParameterState env state pre (count + 1) ∧
      (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block (count + 1)).pp = some next ∧
      Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx nextFrame
        (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block (count + 1)) ∧
      map.Bounded (demandBlockParameterBefore (lowerEnv cfg.mod env.vars results) before bindings block (count + 1)).vals.size ∧
      DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx source.world
        following.typing { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
        ((pre.take (count + 1)).map Prod.fst ++ source.context.inputFuture) map.values map.runs ⟨next, nextFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let innerFrame : GIR.Frame := { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
  let currentBuilder := demandBlockParameterBefore le before bindings block count
  let followingBuilder := demandBlockParameterBefore le before bindings block (count + 1)
  have site : GeneratedBlockParameterInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path, .block, .entry⟩ point (.eff (.slotInit slot id (some origin))) :=
    .slotInit occurrence rows bindingAt atPoint extended
  obtain ⟨value, preAt, valueAt⟩ := cells.binding_at bindingAt
  have preMember : (slot, value) ∈ pre := List.mem_of_getElem? preAt
  obtain ⟨_, _, declaration, variableAt, scopeAt, _, _, _⟩ := source.pretyped.2 slot value preMember
  have root := rootOf_head (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
    rfl variableAt scopeAt
  have innerValue : innerFrame.vals[id]? = some (.val value) := valueAt
  have slotRoot : GIR.slotRoot cx.fn innerFrame slot = pure (.local env.act state.nextScope slot) := by
    change GIR.slotRoot cx.fn { frame with scopes := (block.scope, state.nextScope) :: frame.scopes } slot = _
    rw [slotRoot_eq related slot]
    exact root
  have action : execEff cx.fn innerFrame (.slotInit slot id (some origin)) (demandParameterState env state pre count) =
      .ok innerFrame (demandParameterState env state pre (count + 1)) := by
    simp only [execEff, slotRoot, getVal_of innerValue, pure_bind]
    rw [parameterState_succ preAt]
    rfl
  obtain ⟨current⟩ := source.parameterPrefix count
  obtain ⟨following⟩ := source.parameterPrefix (count + 1)
  have currentCarried := current.retained_inner realized
  have currentDemand : DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx source.world
      current.typing { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
      ((pre.take count).map Prod.fst ++ source.context.inputFuture) map.values map.runs
      ⟨point, innerFrame, demandParameterState env state pre count⟩ := by
    refine ⟨⟨currentBuilder, atPoint, related⟩, current.frame, ?_⟩
    simpa only [RetainedSsaMap.Realizes, innerFrame, demandParameterState] using currentCarried
  refine ⟨site, current, following, coverage, currentDemand, ?_⟩
  cases step with
  | define instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    have equal := Res.ok.inj (execution.symm.trans action)
    rcases equal with ⟨rfl, rfl⟩
    let emitted := emitEffect (.slotInit slot id (some origin)) le currentBuilder
    have emittedRun : emitEffect (.slotInit slot id (some origin)) le currentBuilder = (emitted.1, emitted.2) := rfl
    obtain ⟨sameValues, sameStack, nextPoint, _⟩ :=
      emitEffect_facts emittedRun atPoint (generated_parameter_extended bindingAt extended)
    have followingEq : followingBuilder = emitted.2 := demandBlockParameterBefore_succ bindingAt
    have followingPoint : followingBuilder.pp = some (point.1, point.2 + 1) := by
      rw [followingEq]
      exact nextPoint
    have followingRelated : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx innerFrame followingBuilder := by
      rw [followingEq]
      exact related.stack_eq sameStack
    have followingBounded : map.Bounded followingBuilder.vals.size := by
      rw [followingEq, sameValues]
      exact bounded
    have followingCarried := following.retained_inner realized
    refine ⟨rfl, rfl, rfl, followingPoint, followingRelated, followingBounded,
      ⟨⟨followingBuilder, followingPoint, followingRelated⟩, following.frame, ?_⟩⟩
    simpa only [RetainedSsaMap.Realizes, innerFrame, demandParameterState] using followingCarried
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
