import Goose.Lower.DemandSliceAssignmentEntry
import Goose.Lower.DemandBooleanNext

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_slice_assignment_destination_prefix {cfg : Cfg} {env : Env} {state : St}
    {reference value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference) value origin) state)
    {ty : Ty} (slice : sliceRefTy source.typingEnv reference = some ty)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (beforeAddress : taken < 2)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ destination : PlaceSource cfg env (.deref reference) state,
      source.PlaceChildAt destination rfl ∧
      DemandFrameAt cfg env cx destination.world destination.typingEnv destination.rootsEnv
        destination.context.inputFuture map.values map.runs reached ∧
      ∃ next, ∀ fuel, DemandInstructionStep cx fuel reached next := by
  obtain ⟨location, point, frame, alias, destination, canonical, placed, executed, traversal, post, query,
    child, childAt, childOwner, valueOccurrence, valueRows, nextCoverage, nextBounded, nextAdmitted, nextRealized, nextInput⟩ :=
    accepted_generated_slice_assignment_entry source slice selected owned occurrence rows coverage admitted bounded realized input extended
  exact ⟨destination, canonical, traversal.runtimePrefix_invariant (by omega) steps,
    traversal.runtimePrefix_next beforeAddress steps⟩

theorem accepted_generated_slice_assignment_destination_noStop {cfg : Cfg} {env : Env} {state : St}
    {reference value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference) value origin) state)
    {ty : Ty} (slice : sliceRefTy source.typingEnv reference = some ty)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {reached : DemandRuntimePoint} (beforeAddress : taken < 2)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) : False := by
  obtain ⟨destination, canonical, demanded, next, progress⟩ :=
    accepted_generated_slice_assignment_destination_prefix source slice selected owned occurrence rows coverage admitted bounded
      realized input extended beforeAddress steps
  exact stopped.excludes_step_nonTimeout nonTimeout (progress targetFuel)

#print axioms accepted_generated_slice_assignment_destination_prefix
#print axioms accepted_generated_slice_assignment_destination_noStop
end Goose.Lower
