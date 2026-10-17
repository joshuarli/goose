import Goose.Lower.Validation.ReplacementContentFlowSourceReadyDefinitions
import Goose.Lower.Validation.ReplacementEmissionMap
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

structure SourceReadyFrame (module : GIR.Module) (callees : Array State) (func : Func)
    (types : Array (Option VTy)) (state : State) (completed : LS) : Prop where
  fixed : round module callees func types state = state
  shape : state.Shape func
  blocks : func.blocks = finishBlocks completed.blocks
  values : completed.vals.size = func.numValues

def ReadyOperands (state : State) (instruction : Inst) : Prop :=
  (∀ value ∈ instruction.uses, flowAt state.values value ≠ .pending) ∧
    (∀ value ∈ loadedResults instruction,
      flowAt state.values value ≠ .pending)

def SourceReadyBuilder (state : State) (builder : LS) : Prop :=
  ∀ instruction ∈ builder.insts, ReadyOperands state instruction

def ValueReadyAt (state : State) (action : B ValueId) (env : LEnv) (before : LS) : Prop :=
  EmitsOnly (ReadyOperands state) before (action env before).2 ∧
    ((action env before).2.cur.isSome = true → flowAt state.values (action env before).1 ≠ .pending)

def ValuesReadyAt (state : State) (action : B (List ValueId)) (env : LEnv) (before : LS) : Prop :=
  EmitsOnly (ReadyOperands state) before (action env before).2 ∧
    ((action env before).2.cur.isSome = true →
      ∀ value ∈ (action env before).1, flowAt state.values value ≠ .pending)

theorem SourceReadyFrame.fixed_instruction {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed fragment : LS}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : fragment.Ext completed) {instruction : Inst} (member : instruction ∈ fragment.insts) :
    step module callees func types state instruction = state := by
  have retained := extension_inst_member extension member
  obtain ⟨body, bodyMember, instructionMember⟩ := List.mem_flatMap.mp retained
  let block : GIR.Block := ⟨body.params, body.insts.toList⟩
  have finalMember : block ∈ func.blocks.toList := by
    rw [frame.blocks]
    simp only [finishBlocks, Array.toList_map]
    exact List.mem_map.mpr ⟨body, bodyMember, rfl⟩
  exact round_fixed_step module callees func types state frame.fixed block finalMember instruction instructionMember

theorem SourceReadyBuilder.of_emits {state : State} {before after : LS}
    (ready : SourceReadyBuilder state before) (emitted : EmitsOnly (ReadyOperands state) before after) :
    SourceReadyBuilder state after := by
  intro instruction member
  obtain ⟨body, bodyMember, instructionMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  by_cases old : index < before.blocks.size
  · let previous := before.blocks[index]
    have previousAt : before.blocks[index]? = some previous := by simp [previous, old]
    obtain ⟨next, nextAt, _, tail, appended, tailReady⟩ := emitted.old index previous previousAt
    have same : next = body := Option.some.inj (nextAt.symm.trans row)
    subst next
    rw [appended] at instructionMember
    rcases List.mem_append.mp instructionMember with prior | fresh
    · exact ready instruction (List.mem_flatMap.mpr
        ⟨previous, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previousAt), prior⟩)
    · exact tailReady instruction fresh
  · exact emitted.fresh index body row (Nat.le_of_not_gt old) instruction instructionMember

theorem SourceReadyBuilder.refReady {state : State} {builder : LS} {types : Array (Option VTy)}
    (ready : SourceReadyBuilder state builder)
    (typed : ∀ instruction ∈ builder.insts, ∀ value ∈ instruction.uses,
      ∃ type, types[value]? = some (some type)) :
    ∀ instruction ∈ builder.insts, refReady types state instruction = true := by
  intro instruction member
  exact refReady_of_operands (typed instruction member)
    (fun value use _ => (ready instruction member).1 value use)

#print axioms SourceReadyFrame.fixed_instruction
#print axioms SourceReadyBuilder.of_emits
#print axioms SourceReadyBuilder.refReady

end Goose.Lower.Validation.ReplacementContentFlowSource
