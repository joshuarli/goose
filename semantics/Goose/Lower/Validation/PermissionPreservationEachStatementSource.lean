import Goose.Lower.Validation.PermissionPreservationEachSynthetic
import Goose.Lower.Validation.PermissionPreservationSourceTables
import Goose.Lower.Validation.PermissionInstructionStorageSourceBase
import Goose.Lower.Validation.PermissionInstructionControlEachStatement

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permissionInstructions_forEach_source
    {env output : Core.TEnv} {scope start finish : Nat} {slot : VarId} {index : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    (source : Core.tyStmt env scope (.forEach slot index view byRef body origin) start = .ok (output, finish))
    {func : Func} {results : List Ty} (tables : PermissionSourceTables env results func)
    {first : Nat} {loop : Option LoopCtx} {before after : LS} {result : Unit}
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (viewChild : PermissionStorageViewChild env func results view)
    (bodyChild : ∀ {type : Ty} {start finish : Nat},
      Core.tyBlock {env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible}
        [] body start = .ok (type, finish) →
      ∀ {input output : LS} {value : ValueId} {pre : List (SlotId × ValueId × OriginId)} {loop : Option LoopCtx},
        GeneratedBuilderState input → LoopBuilderFrames loop input → first ≤ input.vals.size →
        (∀ entry ∈ pre, ∀ descriptor, func.slots[entry.1]? = some descriptor →
          PermissionTransfer env.mod.profile (FreshWritableEvidence (lowerEnv env.mod env.vars results) first input)
            (FreshContentsEvidence (lowerEnv env.mod env.vars results) first input) entry.2.1 descriptor.ty) →
        lowerBlock loop pre false body (lowerEnv env.mod env.vars results) input = (value, output) →
        NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first input output)
    (run : lowerStmt loop (.forEach slot index view byRef body origin)
      (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewSource, binding, bodySource, _⟩ := tyStmt_forEach_children source
  have localRow := (declare_ok _ _ _ _ _ declared).2.1
  have indexFacts := declareIndex_ok _ _ _ _ _ indexChecked
  apply forEach_newPermissionInstructions generated floor ?_ ?_ run
  · intro owner viewValue sourceState sourceRun
    exact lowerEachSource_newPermissionInstructions view sourceRun (fun value state childRun =>
      (viewChild viewSource generated childRun).weaken floor)
  · intro owner viewValue sourceState sourceRun sourceLive header counter depth exit input value output
      inputGenerated inputLive inputFrames counterTyped inputFloor extension grows types framed bodyRun
    obtain ⟨elementValue, referenced, referenceRun, valueRun⟩ := bind_eq.mp bodyRun
    obtain ⟨boundValue, initialized, bindingRun, blockRun⟩ := bind_eq.mp valueRun
    have sourceIsLive : sourceState.cur.isSome = true := by
      cases current : sourceState.cur with
      | none => exact (sourceLive current).elim
      | some current => rfl
    have synthetic :=  eachSource_body_prefix_permissions (module := lower env.mod) (func := func) viewSource localRow binding sourceRun generated sourceIsLive
      inputGenerated inputLive floor extension grows types framed counterTyped referenceRun bindingRun
    have referencedGenerated := inputGenerated.emitDef _ referenceRun
    have initializedGenerated := referencedGenerated.eachElemValue slot byRef elementValue bindingRun
    have prefixAdvance := (advB_emitDef _ _ _ _ _ referenceRun).ext.trans
      (advB_eachElemValue slot byRef elementValue _ _ _ _ bindingRun).ext
    have initializedFrames := inputFrames.mono prefixAdvance
    have initializedFloor := Nat.le_trans inputFloor (Nat.le_trans (advB_emitDef _ _ _ _ _ referenceRun).vals
      (advB_eachElemValue slot byRef elementValue _ _ _ _ bindingRun).vals)
    have preTransfer : ∀ entry ∈ ((slot,boundValue,origin) ::
        (match index with | some id => [(id,counter,origin)] | none => [])),
        ∀ descriptor, func.slots[entry.1]? = some descriptor →
        PermissionTransfer env.mod.profile
          (FreshWritableEvidence (lowerEnv env.mod env.vars results) first initialized)
          (FreshContentsEvidence (lowerEnv env.mod env.vars results) first initialized) entry.2.1 descriptor.ty := by
      intro entry member descriptor descriptorRow
      rcases List.mem_cons.mp member with same | other
      · subst entry
        rw [tables.slots] at descriptorRow
        have descriptorEq : (⟨localVar.ty,localVar.kind,localVar.scope,slot⟩ : Slot) = descriptor := by
          simpa [lowerEnv, Array.getElem?_mapIdx, localRow] using descriptorRow
        rw [← descriptorEq]
        exact synthetic.2
      · cases index with
        | none => cases other
        | some id =>
          have same : entry = (id,counter,origin) := by simpa using other
          subst entry
          obtain ⟨_, indexVar, indexRow, _, indexType⟩ := indexFacts.2 id rfl
          rw [tables.slots] at descriptorRow
          have descriptorEq : (⟨indexVar.ty,indexVar.kind,indexVar.scope,id⟩ : Slot) = descriptor := by
            simpa [lowerEnv, Array.getElem?_mapIdx, indexRow] using descriptorRow
          simp only [← descriptorEq, indexType, PermissionTransfer]
    have bodyPermissions := bodyChild bodySource initializedGenerated initializedFrames initializedFloor preTransfer blockRun
    exact synthetic.1.compose_framed bodyPermissions blockRun (dense_lowerBlock _ _ false body)
      (advB_lowerBlock _ _ false body) (types_lowerBlock _ _ false body)
      (generatedTargetFrame_lowerBlock _ _ false body) initializedGenerated initializedFrames

#print axioms permissionInstructions_forEach_source

end Goose.Lower.Validation
