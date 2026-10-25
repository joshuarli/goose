import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLeaves
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyHolders
import Goose.GIR.ReplacementContentFlowProofsCanonicalInvariant

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.localRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {env : LEnv} {typingEnv : TEnv} {upper : Prov} {variableId : VarId} {localVar : LocalVar}
    {address value : ValueId} {mutability : Mutability}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types upper)
    (growth : (start func types).Extends state)
    (placeRun : lowerPlace (.var variableId) env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (visible : variableId ∈ typingEnv.visible) (variableRow : typingEnv.vars[variableId]? = some localVar)
    (slots : VisibleSlotsReady typingEnv state)
    (addressBound : address < state.values.size)
    (addressType : types[address]? = some (some (.data (.ref mutability localVar.ty))))
    (valueType : types[value]? = some (some (.data localVar.ty)))
    (addressRoots : rootsAt upper.vals address ⊆ [.local variableId]) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have loadAdvance := adv_emitDef loadRun
  have placeAdvance := adv_emitDef placeRun
  obtain ⟨addressEmits, addressReady⟩ := frame.variablePlace placeRun (loadAdvance.ext.trans extension)
    (Nat.le_trans loadAdvance.vals allocated) bounded
  obtain ⟨loadEmits, valueReady⟩ := frame.emitDef loadRun extension allocated
    (liveBound_of_adv placeAdvance bounded)
    (by intro live operand member; have same : operand = address := by simpa [Op.uses] using member
        subst operand; exact addressReady live)
    (by
      intro live actual same reference
      have sameAddress : actual = address := by cases same; rfl
      subst actual
      have valueId : value = first.vals.size := by
        cases current : first.cur with
        | none => simp [current] at live
        | some block =>
          have actualRun := loadRun
          rw [emitDef_run _ _ current] at actualRun
          exact (Prod.mk.inj actualRun).1.symm
      rw [← valueId] at reference
      have refLike : localVar.ty.isRefLike = true := by
        simpa only [valRefLike, valueType, Option.some.injEq, VTy.refLike] using reference
      have physical := canonical.holderValues address addressBound mutability localVar.ty addressType refLike
      apply holder_content_ready physical (addressReady live)
      · intro slot member
        have sameSlot : slot = variableId := by simpa using addressRoots member
        subst slot
        exact slots variableId visible localVar variableRow refLike
      · intro index _
        exact contents_ready_of_initial_extends growth index)
    (by intro _ fn args origin impossible; cases impossible)
  exact ⟨addressEmits.trans loadEmits, valueReady⟩

theorem SourceReadyFrame.scalarRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {env : LEnv} {place : Place} {address value : ValueId} {type : Ty}
    (frame : SourceReadyFrame module callees func types state completed)
    (placeRun : lowerPlace place env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound first)
    (child : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values address ≠ .pending))
    (valueType : first.cur.isSome = true → types[value]? = some (some (.data type))) (scalar : type.isRefLike = false) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  obtain ⟨loadEmits, valueReady⟩ := frame.emitDef loadRun extension allocated bounded
    (by intro live operand member; have same : operand = address := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by
      intro live actual same reference
      have valueId : value = first.vals.size := by
        cases current : first.cur with
        | none => simp [current] at live
        | some block =>
          have actualRun := loadRun
          rw [emitDef_run _ _ current] at actualRun
          exact (Prod.mk.inj actualRun).1.symm
      rw [← valueId] at reference
      simp [valRefLike, valueType live, VTy.refLike, scalar] at reference)
    (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans loadEmits, valueReady⟩

#print axioms SourceReadyFrame.localRead
#print axioms SourceReadyFrame.scalarRead

end Goose.Lower.Validation.ReplacementContentFlowSource
