import Goose.Lower.DemandGeneratedBlockEnter

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def demandBlockParameterBefore (le : LEnv) (before : LS) (bindings : List (SlotId × ValueId × OriginId))
    (block : Core.Block) (count : Nat) : LS :=
  (initSlots (bindings.take count) le (demandBlockStatementsBefore le before [] block)).2

theorem initSlots_append_run (first rest : List (SlotId × ValueId × OriginId)) (le : LEnv) (before : LS) :
    initSlots (first ++ rest) le before = initSlots rest le (initSlots first le before).2 := by
  induction first generalizing before with
  | nil => simp only [List.nil_append, initSlots, pure_run]
  | cons binding first induction =>
    rcases binding with ⟨slot, id, origin⟩
    simp only [List.cons_append, initSlots, bind_run]
    exact induction _

private theorem all_parameters_run (le : LEnv) (before : LS) (bindings : List (SlotId × ValueId × OriginId))
    (block : Core.Block) : demandBlockStatementsBefore le before bindings block =
      (initSlots bindings le (demandBlockStatementsBefore le before [] block)).2 := by
  simp only [demandBlockStatementsBefore, initSlots, pure_run]

theorem generated_parameter_extended {le : LEnv} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block} {blocks : Array GIR.Block}
    {index : Nat} {slot : SlotId} {id : ValueId} {origin : OriginId}
    (bindingAt : bindings[index]? = some (slot, id, origin))
    (extended : ExtT (lowerBlock loop bindings want block le before).2 blocks) :
    ExtT (emitEffect (.slotInit slot id (some origin)) le
      (demandBlockParameterBefore le before bindings block index)).2 blocks := by
  have parametersExtended := generated_block_parameters_extended extended
  rw [all_parameters_run] at parametersExtended
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp bindingAt
  have split : bindings = bindings.take index ++ (slot, id, origin) :: bindings.drop (index + 1) := by
    calc
      bindings = bindings.take index ++ bindings.drop index := (List.take_append_drop index bindings).symm
      _ = _ := by rw [List.drop_eq_getElem_cons bound, selected]
  rw [split, initSlots_append_run] at parametersExtended
  simp only [initSlots, bind_run] at parametersExtended
  exact parametersExtended.of_adv (advB_initSlots _ _ _ _ _ rfl)

theorem demandBlockParameterBefore_succ {le : LEnv} {before : LS}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {index : Nat} {slot : SlotId} {id : ValueId} {origin : OriginId}
    (bindingAt : bindings[index]? = some (slot, id, origin)) :
    demandBlockParameterBefore le before bindings block (index + 1) =
      (emitEffect (.slotInit slot id (some origin)) le
        (demandBlockParameterBefore le before bindings block index)).2 := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp bindingAt
  unfold demandBlockParameterBefore
  rw [List.take_succ_eq_append_getElem bound, selected, initSlots_append_run]
  simp only [initSlots, bind_run, pure_run]

inductive GeneratedBlockParameterInstruction (module : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop
  | slotInit {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
      {index : Nat} {slot : SlotId} {id : ValueId} {origin : OriginId} {point : Pt} {required : RetainedSsaMap}
      (occurrence : GeneratedDemandOccurrence module function le root path (.block loop bindings want block) before)
      (rows : GeneratedDemandRows module access occurrence required)
      (bindingAt : bindings[index]? = some (slot, id, origin))
      (atPoint : (demandBlockParameterBefore le before bindings block index).pp = some point)
      (extended : ExtT (lowerBlock loop bindings want block le before).2 function.blocks) :
      GeneratedBlockParameterInstruction module access function required ⟨path, .block, .entry⟩ point
        (.eff (.slotInit slot id (some origin)))

theorem GeneratedBlockParameterInstruction.instruction {module : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedBlockParameterInstruction module access function required label point instruction) :
    instAt function point = some instruction := by
  cases site with
  | slotInit occurrence rows bindingAt atPoint extended =>
    simpa only [instAt_eq] using
      (emitEffect_facts rfl atPoint (generated_parameter_extended bindingAt extended)).2.2.2

theorem GeneratedBlockParameterInstruction.source {module : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedBlockParameterInstruction module access function required label point instruction) :
    ∃ (le : LEnv) (root : DemandNode) (before : LS) (loop : Option LoopCtx)
        (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      GeneratedDemandOccurrence module function le root label.path (.block loop bindings want block) before ∧
        label.phase = .block ∧ label.boundary = .entry := by
  cases site with
  | slotInit occurrence rows bindingAt atPoint extended => exact ⟨_, _, _, _, _, _, _, occurrence, rfl, rfl⟩

theorem PreRel.binding_at {frame : GIR.Frame} :
    ∀ {bindings : List (SlotId × ValueId × OriginId)} {pre : List (VarId × Val)}, PreRel frame bindings pre →
      ∀ {index : Nat} {slot : SlotId} {id : ValueId} {origin : OriginId},
        bindings[index]? = some (slot, id, origin) →
        ∃ value, pre[index]? = some (slot, value) ∧ frame.vals[id]? = some (.val value)
  | [], [], _, index, slot, id, origin, selected => by simp at selected
  | (slot, id, origin) :: bindings, (sourceSlot, value) :: pre, ⟨sameSlot, valueAt, rest⟩, index, selectedSlot, selectedId, selectedOrigin, selected => by
    subst sourceSlot
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨rfl, rfl, rfl⟩
      exact ⟨value, rfl, valueAt⟩
    | succ index => exact PreRel.binding_at rest selected
  | [], _ :: _, impossible, _, _, _, _, _ => impossible.elim
  | _ :: _, [], impossible, _, _, _, _, _ => impossible.elim

end Goose.Lower
