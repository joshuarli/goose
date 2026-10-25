import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementControl

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem emitsOnly_joinArms {property : Inst → Prop}
    (terms : ∀ term, property (.term term)) (yes no : Option BlockId) :
    EmitsOnlyRun property (Goose.Lower.joinArms yes no) := by
  unfold Goose.Lower.joinArms
  split
  · exact emitsOnly_setCur property none
  · apply (emitsOnly_newBlock property []).bind
    rintro ⟨join, parameters⟩
    apply EmitsOnlyRun.bind (next := fun _ => Goose.Lower.setCur (some join))
    · induction (yes.toList ++ no.toList) with
      | nil => exact .pure _ _
      | cons block rest ih =>
        exact (emitsOnly_pushInst block (.term (.br join [])) (terms _)).bind fun _ => ih
    · intro _
      exact emitsOnly_setCur property (some join)

theorem OccurrenceSitesBuilder.fork {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper) (condition : ValueId) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.fork condition le before).2 func types upper :=
  checked.of_action (emitsOnly_fork _ (fun _ => trivial) condition) (types_fork condition)
    (generatedTargetFrame_fork none condition) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem OccurrenceSitesBuilder.setCur {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper) (current : Option BlockId) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.setCur current le before).2 func types upper :=
  checked.of_blocks rfl rfl

theorem OccurrenceSitesBuilder.joinArms {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper) (yes no : Option BlockId) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.joinArms yes no le before).2 func types upper :=
  checked.of_action (emitsOnly_joinArms (fun _ => trivial) yes no) (types_joinArms yes no)
    (generatedTargetFrame_joinArms none yes no) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem OccurrenceSitesBuilder.newBlock {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper) (parameters : List VTy) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.newBlock parameters le before).2 func types upper :=
  checked.of_action (emitsOnly_newBlock _ parameters) (types_newBlock parameters)
    (generatedTargetFrame_newBlock none parameters) rfl (Nat.le_refl _) (fun _ _ => rfl)

theorem occurrenceLedger_fork {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (condition : ValueId) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (Goose.Lower.fork condition) :=
  emitsOnly_fork _ occurrenceInstructionTerm condition

theorem occurrenceLedger_joinArms {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (yes no : Option BlockId) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (Goose.Lower.joinArms yes no) :=
  emitsOnly_joinArms occurrenceInstructionTerm yes no

theorem occurrenceLedger_initSlots {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (bindings : List (SlotId × ValueId × OriginId)) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (Goose.Lower.initSlots bindings) := by
  induction bindings with
  | nil => exact .pure _ _
  | cons binding rest ih =>
    exact (emitsOnly_emitEffect _ (InstructionOccurrences.slotInit _ _ _)).bind fun _ => ih

theorem occurrenceSites_initSlots {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (bindings : List (SlotId × ValueId × OriginId))
    (checked : OccurrenceSitesBuilder env root targets le before func types upper) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.initSlots bindings le before).2 func types upper := by
  induction bindings generalizing before with
  | nil => exact checked
  | cons binding rest ih => exact ih (checked.emitEffect (effect := .slotInit binding.1 binding.2.1 (some binding.2.2)) trivial rfl)

#print axioms OccurrenceSitesBuilder.fork
#print axioms OccurrenceSitesBuilder.joinArms

end Goose.Lower.Validation.ReplacementContentFlowSource
