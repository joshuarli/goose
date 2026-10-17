import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadBounds
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before after : LS}
  {provenance : Prov} {results : Array (List RootRef)} {env : LEnv}
  {input output : ValueId} {root : RootRef} {mutability : Mutability}

theorem SourceReadyFrame.native_definition_root
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    {operation : Op} (run : Lower.emitDef operation env before = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (source : root ∈ rootsOfDef results types func provenance output operation) :
    root ∈ rootsAt provenance.vals output := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    obtain ⟨body, member, instruction⟩ := emitted_definition_retained current
      (bounded block current) run extension frame.blocks
    apply provStep_def_roots _ (quiet body member _ instruction) source
    rw [valuesSize]
    exact definitions body member _ _ instruction

theorem SourceReadyFrame.native_freezeTo_root
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    (run : Lower.freezeTo mutability input env before = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed) (source : root ∈ rootsAt provenance.vals input) :
    root ∈ rootsAt provenance.vals output := by
  unfold Lower.freezeTo at run
  obtain ⟨type, classified, classification, tail⟩ := bind_eq.mp run
  have same : classified = before := valTy_eq classification
  subst classified
  split at tail
  · exact frame.native_definition_root valuesSize definitions quiet tail bounded live extension source
  · obtain ⟨rfl, rfl⟩ := pure_eq.mp tail
    exact source

theorem SourceReadyFrame.native_borrowTo_root
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    (run : Lower.borrowTo mutability input env before = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed) (source : root ∈ rootsAt provenance.vals input) :
    root ∈ rootsAt provenance.vals output := by
  have classification : valTy input env before = ((valTy input env before).1, before) :=
    Prod.ext rfl (valTy_eq rfl)
  change (if mutability == .mutable && env.mod.profile == .shrink &&
      (match (valTy input env before).1 with
       | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) => true
       | _ => false) then Lower.emitDef (.ownerBorrow input) else Lower.freezeTo mutability input)
      env (valTy input env before).2 = (output, after) at run
  rw [classification] at run
  by_cases borrowed : (mutability == .mutable && env.mod.profile == .shrink &&
      (match (valTy input env before).1 with
       | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) => true
       | _ => false)) = true
  · rw [if_pos borrowed] at run
    exact frame.native_definition_root valuesSize definitions quiet run bounded live extension source
  · rw [if_neg borrowed] at run
    exact frame.native_freezeTo_root valuesSize definitions quiet run bounded live extension source

theorem SourceReadyFrame.native_variable_argument_root
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    {variableId : VarId}
    (run : lowerArg (.byRef mutability (.var variableId)) env before = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed) : RootRef.local variableId ∈ rootsAt provenance.vals output := by
  let address := Lower.emitDef (.slotAddr variableId) env before
  have tail : Lower.borrowTo mutability address.1 env address.2 = (output, after) := by
    simpa only [lowerArg, lowerPlace, bind_run, address] using run
  have addressRun : Lower.emitDef (.slotAddr variableId) env before = address := rfl
  have advance := adv_emitDef addressRun
  have addressExtension : address.2.Ext completed :=
    (advB_borrowTo mutability address.1 env address.2 output after tail).ext.trans extension
  have member := frame.native_definition_root valuesSize definitions quiet addressRun bounded live
    addressExtension (show RootRef.local variableId ∈ rootsOfDef results types func provenance address.1 (.slotAddr variableId) from by simp [rootsOfDef])
  have addressLive : address.2.cur.isSome = true := by
    cases current : before.cur with
    | none => simp [current] at live
    | some block => simp [address, emitDef_run _ _ current, current]
  exact frame.native_borrowTo_root valuesSize definitions quiet tail
    (liveBound_of_adv advance bounded) addressLive extension member

theorem SourceReadyFrame.native_forwarded_argument_root
    (frame : SourceReadyFrame module callees func types state completed)
    (valuesSize : provenance.vals.size = func.numValues)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < func.numValues)
    (quiet : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      func.provStep results types (provenance, false) instruction = (provenance, false))
    {variableId : VarId} {address holder : ValueId} {first middle : LS}
    (slotRun : Lower.emitDef (.slotAddr variableId) env before = (address, first))
    (loadRun : Lower.emitDef (.load address) env first = (holder, middle))
    (borrowRun : Lower.borrowTo mutability holder env middle = (output, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext completed)
    (seed : RootRef.param variableId ∈ rootsAt provenance.slots variableId)
    (reference : valRefLike types holder = true) :
    RootRef.param variableId ∈ rootsAt provenance.vals output := by
  have borrowAdvance := advB_borrowTo mutability holder env middle output after borrowRun
  have middleExtension := borrowAdvance.ext.trans extension
  have loadAdvance := adv_emitDef loadRun
  have firstExtension := loadAdvance.ext.trans middleExtension
  have slotMember := frame.native_definition_root valuesSize definitions quiet slotRun bounded live firstExtension
    (show RootRef.local variableId ∈ rootsOfDef results types func provenance address (.slotAddr variableId) from by simp [rootsOfDef])
  have slotAdvance := adv_emitDef slotRun
  have firstBound := liveBound_of_adv slotAdvance bounded
  have firstLive : first.cur.isSome = true := by
    cases current : before.cur with
    | none => simp [current] at live
    | some block =>
      have actual := slotRun
      rw [emitDef_run _ _ current] at actual
      simpa only [current, Option.isSome_some] using congrArg (fun pair => pair.2.cur.isSome) actual.symm
  have middleLive : middle.cur.isSome = true := by
    cases current : first.cur with
    | none => simp [current] at firstLive
    | some block =>
      have actual := loadRun
      rw [emitDef_run _ _ current] at actual
      simpa only [current, Option.isSome_some] using congrArg (fun pair => pair.2.cur.isSome) actual.symm
  have holderMember : RootRef.param variableId ∈ rootsAt provenance.vals holder := by
    apply frame.native_definition_root valuesSize definitions quiet loadRun firstBound firstLive middleExtension
    simp only [rootsOfDef, reference, ite_true]
    apply (unionRoots_mem_iff _ _ _).mpr
    exact Or.inl (List.mem_flatMap.mpr ⟨.local variableId, slotMember, seed⟩)
  exact frame.native_borrowTo_root valuesSize definitions quiet borrowRun
    (liveBound_of_adv loadAdvance firstBound) middleLive extension holderMember

#print axioms SourceReadyFrame.native_forwarded_argument_root

#print axioms SourceReadyFrame.native_variable_argument_root

#print axioms SourceReadyFrame.native_definition_root
#print axioms SourceReadyFrame.native_freezeTo_root
#print axioms SourceReadyFrame.native_borrowTo_root

end Goose.Lower.Validation.ReplacementContentFlowSource
