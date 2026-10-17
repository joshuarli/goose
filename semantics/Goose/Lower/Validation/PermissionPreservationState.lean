import Goose.Lower.Validation.PermissionPreservationRuleTransport
import Goose.Lower.Validation.PermissionPreservationLowered

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def PermissionInstruction (module : GIR.Module) (func : Func) (le : LEnv) (state : LS)
    (instruction : Inst) : Prop :=
  PermissionRule module func state.vals (WritableEvidence le state) (ContentsEvidence le state) instruction ∧
    PermissionGuardTypes state.vals instruction

def PermissionState (module : GIR.Module) (func : Func) (le : LEnv) (state : LS) : Prop :=
  ∀ instruction ∈ state.insts, PermissionInstruction module func le state instruction

theorem PermissionInstruction.retained {module : GIR.Module} {func : Func} {le : LEnv}
    {before after : LS} {instruction : Inst} {loop : Option LoopCtx}
    (permitted : PermissionInstruction module func le before instruction)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) :
    PermissionInstruction module func le after instruction := by
  constructor
  · apply (permitted.1.retained permitted.2 types).mono
    · intro value evidence
      exact evidence.ext beforeDense afterDense extension grows types frames framed
    · intro value evidence
      exact evidence.ext beforeDense afterDense extension grows types frames framed
  · exact permitted.2.retained types

theorem PermissionState.retained {module : GIR.Module} {func : Func} {le : LEnv}
    {before after : LS} {loop : Option LoopCtx}
    (permitted : PermissionState module func le before)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) :
    ∀ instruction ∈ before.insts, PermissionInstruction module func le after instruction := by
  intro instruction member
  exact (permitted instruction member).retained beforeDense afterDense extension grows types frames framed

theorem PermissionState.of_run {α : Type} {action : B α} {module : GIR.Module} {func : Func}
    {le : LEnv} {before after : LS} {result : α} {loop : Option LoopCtx}
    (permitted : PermissionState module func le before) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after) :
    ∀ instruction ∈ before.insts, PermissionInstruction module func le after instruction := by
  have afterDense := (dense le before result after run beforeDense bounded).1
  have advanced := advances le before result after run
  exact permitted.retained beforeDense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem PermissionState.of_framed_run {α : Type} {action : B α} {module : GIR.Module} {func : Func}
    {le : LEnv} {before after : LS} {result : α} {loop : Option LoopCtx}
    (permitted : PermissionState module func le before) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) :
    ∀ instruction ∈ before.insts, PermissionInstruction module func le after instruction := by
  have framed := (frameRun before le before result after (.refl _) frames (.refl loop before) run).1
  exact permitted.of_run run dense advances typed beforeDense bounded frames framed

theorem PermissionState.initState (module : GIR.Module) (func : Func) (le : LEnv) :
    PermissionState module func le initState := by
  intro instruction member
  simp [LS.insts, Goose.Lower.initState] at member

theorem PermissionState.check {module : Core.Module} {vars : Array LocalVar} {results : List Ty}
    {state : LS} {func : Func}
    (permitted : PermissionState (lower module) func (lowerEnv module vars results) state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = (lowerEnv module vars results).slots) (label : String) :
    checkPermissions (lower module) label func state.vals = .ok () := by
  apply checkPermissions_lowered_function blocks slots
  intro block blockMember instruction member
  have flattened : func.blocks.toList.flatMap (·.insts) = state.insts := by
    rw [blocks]
    simp only [finishBlocks, Array.toList_map, List.flatMap_map, LS.insts]
  apply (permitted instruction ?_).1
  rw [← flattened]
  exact List.mem_flatMap.mpr ⟨block, blockMember, member⟩

theorem PermissionState.check_reconstructed {module : Core.Module} {vars : Array LocalVar}
    {results : List Ty} {state : LS} {func : Func} {types : Array (Option VTy)}
    (permitted : PermissionState (lower module) func (lowerEnv module vars results) state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = (lowerEnv module vars results).slots)
    (reconstructed : types = state.vals) (label : String) :
    checkPermissions (lower module) label func types = .ok () := by
  rw [reconstructed]
  exact permitted.check blocks slots label

#print axioms PermissionInstruction.retained
#print axioms PermissionState.check
#print axioms PermissionState.check_reconstructed

end Goose.Lower.Validation
