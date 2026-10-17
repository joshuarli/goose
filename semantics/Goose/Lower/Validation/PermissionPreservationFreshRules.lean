import Goose.Lower.Validation.PermissionPreservationState
import Goose.Lower.Validation.PermissionPreservationPatch

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FreshPermissionInstruction (module : GIR.Module) (func : Func) (le : LEnv) (first : Nat)
    (state : LS) (instruction : Inst) : Prop :=
  PermissionRule module func state.vals (FreshWritableEvidence le first state)
    (FreshContentsEvidence le first state) instruction ∧ PermissionGuardTypes state.vals instruction

def NewPermissionInstructions (module : GIR.Module) (func : Func) (le : LEnv) (first : Nat)
    (before after : LS) : Prop :=
  ∀ instruction ∈ after.insts,
    instruction ∈ before.insts ∨ FreshPermissionInstruction module func le first after instruction

theorem FreshPermissionInstruction.forget {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {instruction : Inst}
    (permitted : FreshPermissionInstruction module func le first state instruction) :
    PermissionInstruction module func le state instruction :=
  ⟨permitted.1.mono (fun _ evidence => evidence.forget) (fun _ evidence => evidence.forget), permitted.2⟩

theorem FreshPermissionInstruction.weaken {module : GIR.Module} {func : Func} {le : LEnv}
    {first earlier : Nat} {state : LS} {instruction : Inst}
    (permitted : FreshPermissionInstruction module func le first state instruction) (bound : earlier ≤ first) :
    FreshPermissionInstruction module func le earlier state instruction :=
  ⟨permitted.1.mono (fun _ evidence => evidence.weaken bound) (fun _ evidence => evidence.weaken bound), permitted.2⟩

theorem FreshPermissionInstruction.retained {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {loop : Option LoopCtx}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) :
    FreshPermissionInstruction module func le first after instruction := by
  constructor
  · apply (permitted.1.retained permitted.2 types).mono
    · intro value evidence
      exact evidence.ext beforeDense afterDense extension grows types frames framed
    · intro value evidence
      exact evidence.ext beforeDense afterDense extension grows types frames framed
  · exact permitted.2.retained types

theorem FreshPermissionInstruction.patchTerm_before {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {current : BlockId}
    {result : Unit} {term : Term}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchTerm current term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshPermissionInstruction module func le first after instruction := by
  have types := types_patchTerm current term le before result after run
  constructor
  · apply (permitted.1.retained permitted.2 types).mono
    · intro value evidence
      exact evidence.patchTerm_before checked bounded run targets
    · intro value evidence
      exact evidence.patchTerm_before checked bounded run targets
  · exact permitted.2.retained types

theorem FreshPermissionInstruction.emitTerm_before {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {result : Unit} {term : Term}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitTerm term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshPermissionInstruction module func le first after instruction := by
  have types := types_emitTerm term le before result after run
  constructor
  · apply (permitted.1.retained permitted.2 types).mono
    · intro value evidence
      exact evidence.emitTerm_before checked bounded run targets
    · intro value evidence
      exact evidence.emitTerm_before checked bounded run targets
  · exact permitted.2.retained types

theorem NewPermissionInstructions.weaken {module : GIR.Module} {func : Func} {le : LEnv}
    {first earlier : Nat} {before after : LS}
    (permitted : NewPermissionInstructions module func le first before after) (bound : earlier ≤ first) :
    NewPermissionInstructions module func le earlier before after := by
  intro instruction member
  exact (permitted instruction member).imp id (fun issued => issued.weaken bound)

theorem NewPermissionInstructions.compose {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS}
    (firstRun : NewPermissionInstructions module func le first before middle)
    (secondRun : NewPermissionInstructions module func le first middle after)
    (retained : ∀ instruction ∈ middle.insts,
      FreshPermissionInstruction module func le first middle instruction →
      FreshPermissionInstruction module func le first after instruction) :
    NewPermissionInstructions module func le first before after := by
  intro instruction member
  rcases secondRun instruction member with old | issued
  · rcases firstRun instruction old with original | issued
    · exact Or.inl original
    · exact Or.inr (retained instruction old issued)
  · exact Or.inr issued

theorem NewPermissionInstructions.finish {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS}
    (issued : NewPermissionInstructions module func le first before after)
    (retained : ∀ instruction ∈ before.insts, PermissionInstruction module func le after instruction) :
    PermissionState module func le after := by
  intro instruction member
  exact (issued instruction member).elim (retained instruction) FreshPermissionInstruction.forget

#print axioms FreshPermissionInstruction.retained
#print axioms FreshPermissionInstruction.emitTerm_before
#print axioms NewPermissionInstructions.compose
#print axioms NewPermissionInstructions.finish

end Goose.Lower.Validation
