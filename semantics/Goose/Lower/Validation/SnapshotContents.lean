import Goose.Lower.Validation.ExpressionTypingFreshContents
import Goose.Lower.Validation.JoinContentsGraph
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure SnapshotContentsWitness (le : LEnv) (first snapshot owner : ValueId)
    (authorized : ValueId → Prop) (state : LS) : Prop where
  closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
    (permissionFunc le state) state.vals authorized
  noninteger : NonIntegerParameters (permissionFunc le state) authorized
  ownerMember : authorized owner
  fresh : ∀ candidate, authorized candidate → first ≤ candidate
  beforeSnapshot : ∀ candidate, authorized candidate → candidate < snapshot

theorem SnapshotContentsWitness.ext {le : LEnv} {first snapshot owner : ValueId}
    {authorized : ValueId → Prop} {before after : LS} {loop : Option LoopCtx}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  refine ⟨witness.closed.ext beforeDense afterDense extension grows types frames framed witness.noninteger,
    ?_, witness.ownerMember, witness.fresh, witness.beforeSnapshot⟩
  apply witness.noninteger.ext beforeDense afterDense extension
  intro candidate member
  simpa only [permissionFunc_numValues beforeDense le] using witness.closed.bounded candidate member

theorem SnapshotContentsWitness.of_framed_run {α : Type} {action : B α} {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {result : α} {loop : Option LoopCtx}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  have afterDense := (dense le before result after run generated.dense generated.live).1
  have advanced := advances le before result after run
  have framed := (frameRun before le before result after (.refl _) frames (.refl loop before) run).1
  exact witness.ext generated.dense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem snapshotContentsWitness_emit {le : LEnv} {before after : LS}
    {first owner snapshot : ValueId} {mode : SnapshotMode} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (generated : GeneratedBuilderState before) (live : before.cur = some current)
    (run : emitDef (.snapshot mode owner) le before = (snapshot, after)) :
    ∃ authorized, SnapshotContentsWitness le first snapshot owner authorized after := by
  obtain ⟨authorized, closed, noninteger, member, fresh⟩ := evidence
  have valueEq := (emitDef_fresh_size live run).1
  have witness : SnapshotContentsWitness le first snapshot owner authorized before := by
    refine ⟨closed, noninteger, member, fresh, ?_⟩
    intro candidate permitted
    rw [valueEq]
    simpa only [permissionFunc_numValues generated.dense le] using closed.bounded candidate permitted
  exact ⟨authorized, witness.of_framed_run run (dense_emitDef _) (advB_emitDef _)
    (types_emitDef _) (generatedTargetFrame_emitDef none _) generated trivial⟩

theorem SnapshotContentsWitness.patchBrs_avoiding_target {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {target : BlockId} {result : Unit} (incoming : List (BlockId × ValueId))
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (generated : GeneratedBuilderState before)
    (run : patchBrs target incoming le before = (result, after))
    (excluded : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, ¬ authorized parameter.1) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  exact ⟨witness.closed.patchBrs_avoiding_target incoming generated.dense generated.live run excluded,
    witness.noninteger.patchBrs incoming run, witness.ownerMember, witness.fresh, witness.beforeSnapshot⟩

theorem SnapshotContentsWitness.patchBrs_before {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {target : BlockId} {result : Unit} (incoming : List (BlockId × ValueId))
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (generated : GeneratedBuilderState before)
    (run : patchBrs target incoming le before = (result, after))
    (earlier : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  apply witness.patchBrs_avoiding_target incoming generated run
  intro destination row parameter member permitted
  exact Nat.not_lt_of_ge (witness.fresh parameter.1 permitted) (earlier destination row parameter member)

theorem SnapshotContentsWitness.patchBrs_after {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {target : BlockId} {result : Unit} (incoming : List (BlockId × ValueId))
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (generated : GeneratedBuilderState before)
    (run : patchBrs target incoming le before = (result, after))
    (later : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, snapshot ≤ parameter.1) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  apply witness.patchBrs_avoiding_target incoming generated run
  intro destination row parameter member permitted
  exact Nat.not_lt_of_ge (later destination row parameter member) (witness.beforeSnapshot parameter.1 permitted)

end Goose.Lower.Validation
