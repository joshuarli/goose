import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSiteTargets
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsBasic

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem occurrenceInstructionTerm {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (term : Term) :
    InstructionOccurrences env root func types upper (.term term) :=
  InstructionOccurrences.term env root func types upper term

theorem InstructionOccurrences.enter {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (scope : ScopeId) :
    InstructionOccurrences env root func types upper (.eff (.enter scope)) := by
  simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses]

theorem InstructionOccurrences.leave {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (scope : ScopeId) :
    InstructionOccurrences env root func types upper (.eff (.leave scope)) := by
  simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses]

theorem InstructionOccurrences.slotInit {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (slot : SlotId) (value : ValueId) (origin : Option OriginId) :
    InstructionOccurrences env root func types upper (.eff (.slotInit slot value origin)) := by
  simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses]

theorem InstructionOccurrences.next {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (result value : ValueId) (type : IntTy)
    (scalar : valRefLike types value = false) :
    InstructionOccurrences env root func types upper (.def result (.next type value)) := by
  constructor
  · intro operand member reference
    have same : operand = value := by
      simpa only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] using member
    subst operand
    rw [scalar] at reference
    cases reference
  · refine ⟨?_, ?_, InstructionOccurrences.no_store (by intro address value origin same; cases same), ?_⟩
    · intro loaded address same
      cases (Inst.def.inj same).2
    · intro loaded callee args origin same
      cases (Inst.def.inj same).2
    · intro operand member mutability payload row
      have same : operand = value := by
        simpa only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] using member
      subst operand
      have reference : valRefLike types value = true := by simp [valRefLike, row, VTy.refLike, Ty.isRefLike]
      rw [scalar] at reference
      cases reference

theorem OccurrenceSitesBuilder.ghost_retained {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    (checked : OccurrenceSitesBuilder env root targets le state func types old)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    OccurrenceSitesBuilder env root targets le state func types next :=
  checked.of_emits (.refl _ _) (.refl _) (.of_blocks rfl) growth retained

theorem OccurrenceSitesBuilder.of_action {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {action : B α} {result : α}
    (checked : OccurrenceSitesBuilder env root targets le before func types old)
    (emitted : EmitsOnlyRun NotReplacement action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun none action) (run : action le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    OccurrenceSitesBuilder env root targets le after func types next :=
  checked.of_emits (emitted le before result after run) (typed le before result after run)
    (.of_run framed run) growth retained

theorem OccurrenceSitesBuilder.emitEffect {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {effect : Effect} {result : Unit}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper)
    (ordinary : NotReplacement (.eff effect)) (run : emitEffect effect le before = (result, after)) :
    OccurrenceSitesBuilder env root targets le after func types upper :=
  checked.of_action (emitsOnly_emitEffect effect ordinary) (types_emitEffect effect)
    (generatedTargetFrame_emitEffect none effect) run (Nat.le_refl _) (fun _ _ => rfl)

theorem OccurrenceSitesBuilder.emitTerm {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {term : Term} {result : Unit}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target)
    (run : emitTerm term le before = (result, after)) :
    OccurrenceSitesBuilder env root targets le after func types upper :=
  checked.of_emits (emitsOnly_emitTerm term trivial le before result after run)
    (types_emitTerm term le before result after run) (.emitTerm run allowed)
    (Nat.le_refl _) (fun _ _ => rfl)

theorem OccurrenceSitesBuilder.of_blocks {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le before func types upper)
    (blocks : after.blocks = before.blocks) (values : after.vals = before.vals) :
    OccurrenceSitesBuilder env root targets le after func types upper :=
  checked.of_emits (.of_blocks blocks) (by intro value type row; simpa only [values] using row)
    (.of_blocks blocks) (Nat.le_refl _) (fun _ _ => rfl)

theorem occurrenceLedger_leaveAll {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (scopes : List ScopeId) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (Goose.Lower.leaveAll scopes) := by
  induction scopes with
  | nil => exact .pure _ _
  | cons scope rest ih => exact (emitsOnly_emitEffect _ (InstructionOccurrences.leave scope)).bind fun _ => ih

theorem occurrenceSites_leaveAll {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (scopes : List ScopeId) (checked : OccurrenceSitesBuilder env root targets le before func types upper) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.leaveAll scopes le before).2 func types upper := by
  induction scopes generalizing before with
  | nil => exact checked
  | cons scope rest ih => exact ih (checked.emitEffect (effect := .leave scope) trivial rfl)

#print axioms OccurrenceSitesBuilder.of_action
#print axioms occurrenceLedger_leaveAll

end Goose.Lower.Validation.ReplacementContentFlowSource
