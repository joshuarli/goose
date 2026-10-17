import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLocalReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.contentRead {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first middle after : LS}
    {env : LEnv} {typingEnv : TEnv} {upper : Prov} {variableId : VarId} {localVar : LocalVar}
    {slotAddress holder value : ValueId} {slotMutability mutability sliceMutability : Mutability} {element : Ty}
    (frame : SourceReadyFrame module callees func types state completed)
    (canonical : state.CanonicalWithin func types upper)
    (growth : (start func types).Extends state)
    (placeRun : lowerPlace (.var variableId) env before = (slotAddress, first))
    (innerRun : Lower.emitDef (.load slotAddress) env first = (holder, middle))
    (outerRun : Lower.emitDef (.load holder) env middle = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (visible : variableId ∈ typingEnv.visible) (variableRow : typingEnv.vars[variableId]? = some localVar)
    (slots : VisibleSlotsReady typingEnv state)
    (slotBound : slotAddress < state.values.size) (holderBound : holder < state.values.size)
    (slotType : types[slotAddress]? = some (some (.data (.ref slotMutability localVar.ty))))
    (innerType : types[holder]? = some (some (.data localVar.ty)))
    (holderType : types[holder]? = some (some (.data (.ref mutability (.slice sliceMutability element)))))
    (slotRoots : rootsAt upper.vals slotAddress ⊆ [.local variableId])
    (holderRoots : rootsAt upper.vals holder ⊆ [.param variableId]) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have outerAdvance := adv_emitDef outerRun
  obtain ⟨innerEmits, innerReady⟩ := frame.localRead canonical growth placeRun innerRun
    (outerAdvance.ext.trans extension) (Nat.le_trans outerAdvance.vals allocated) bounded visible variableRow
    slots slotBound slotType innerType slotRoots
  have middleBound := liveBound_of_adv (adv_emitDef innerRun)
    (liveBound_of_adv (adv_emitDef placeRun) bounded)
  obtain ⟨outerEmits, outerReady⟩ := frame.emitDef outerRun extension allocated middleBound
    (by intro live operand member; have same : operand = holder := by simpa [Op.uses] using member
        subst operand; exact innerReady live)
    (by
      intro live actual same _
      have sameAddress : actual = holder := by cases same; rfl
      subst actual
      have physical := canonical.holderValues holder holderBound mutability
        (.slice sliceMutability element) holderType rfl
      apply holder_parameter_content_ready growth physical (innerReady live)
      intro slot member
      simpa using holderRoots member)
    (by intro _ fn args origin impossible; cases impossible)
  exact ⟨innerEmits.trans outerEmits, outerReady⟩

#print axioms SourceReadyFrame.contentRead

end Goose.Lower.Validation.ReplacementContentFlowSource
