import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsBasic

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem OperandOccurrence.place {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {place : Place} {before after : RState} {roots : List RootRef} {value : ValueId} {path : List Nat}
    (source : DemandNodeAt root path (.place place)) (replay : rpPlace env place before = .ok (roots, after))
    (bound : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .place place, before, roots, after, source, .place rfl replay, bound, refined⟩

theorem OperandOccurrence.expression {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {expression : Expr} {before after : RState} {roots : List RootRef} {value : ValueId} {path : List Nat}
    (source : DemandNodeAt root path (.expression expression)) (replay : rpExpr env expression before = .ok (roots, after))
    (bound : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .expression expression, before, roots, after, source, .expression rfl replay, bound, refined⟩

theorem OperandOccurrence.view {env : PEnv} {root : DemandNode} {func : Func} {upper : Prov}
    {view : View} {before after : RState} {roots : List RootRef} {value : ValueId} {path : List Nat}
    (source : DemandNodeAt root path (.view view)) (replay : rpView env view before = .ok (roots, after))
    (bound : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
    OperandOccurrence env root func upper value :=
  ⟨path, .view view, before, roots, after, source, .view rfl replay, bound, refined⟩

theorem InstructionOccurrences.effect {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {effect : Effect}
    (operands : ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands (.eff effect),
      valRefLike types value = true → OperandOccurrence env root func upper value)
    (ordinary : ∀ address value origin, effect ≠ .store address value origin)
    (consumed : ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands (.eff effect),
      ∀ mutability payload, types[value]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper value) :
    InstructionOccurrences env root func types upper (.eff effect) := by
  exact ⟨operands, by intros; contradiction, by intros; contradiction,
    InstructionOccurrences.no_store (by intro address value origin same; exact ordinary address value origin (Inst.eff.inj same)), consumed⟩

theorem InstructionOccurrences.definition {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {value : ValueId} {op : Op}
    (operands : ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def value op),
      valRefLike types operand = true → OperandOccurrence env root func upper operand)
    (notLoad : ∀ address, op ≠ .load address) (notCall : ∀ fn args origin, op ≠ .call fn args origin)
    (consumed : ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def value op),
      ∀ mutability payload, types[operand]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper operand) :
    InstructionOccurrences env root func types upper (.def value op) := by
  refine ⟨operands, ?_, ?_, InstructionOccurrences.no_store (by intro address value origin same; cases same), consumed⟩
  · intro result address same _
    exact (notLoad address (Inst.def.inj same).2).elim
  · intro result fn args origin same
    exact (notCall fn args origin (Inst.def.inj same).2).elim

theorem InstructionOccurrences.store {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {address value : ValueId} {origin : Option OriginId}
    (operands : ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.eff (.store address value origin)),
      valRefLike types operand = true → OperandOccurrence env root func upper operand)
    (stored : valRefLike types value = true → StoreOccurrence env root func upper address value origin)
    (consumed : ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.eff (.store address value origin)),
      ∀ mutability payload, types[operand]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper operand) :
    InstructionOccurrences env root func types upper (.eff (.store address value origin)) := by
  refine ⟨operands, by intros; contradiction, by intros; contradiction, ?_, consumed⟩
  intro address' value' origin' same reference
  cases same
  exact stored reference

theorem occurrence_emitEffect_live {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {le : LEnv} {before after : LS} {value : Unit} {effect : Effect}
    (run : emitEffect effect le before = (value, after))
    (valid : before.cur.isSome = true → InstructionOccurrences env root func types upper (.eff effect)) :
    OccurrenceLedger env root func types upper before after := by
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact .refl _ _
  | some block => exact emitsOnly_emitEffect effect (valid (by simp [current])) le before value after run

theorem OccurrenceSitesBuilder.mutationEffect {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {result : Unit} {effect : Effect}
    (checked : OccurrenceSitesBuilder env root targets le before func types old)
    (notReplacement : NotReplacement (.eff effect))
    (run : emitEffect effect le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    OccurrenceSitesBuilder env root targets le after func types next :=
  checked.of_emits (emitsOnly_emitEffect effect notReplacement le before result after run)
    (types_emitEffect effect le before result after run)
    (.of_run (generatedTargetFrame_emitEffect none effect) run) growth retained

end Goose.Lower.Validation.ReplacementContentFlowSource
