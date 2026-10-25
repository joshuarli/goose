import Goose.Lower.Validation.SourceTouchSummaryBounds
import Goose.Lower.Validation.ValidationTypedModuleInstructions
import Goose.Lower.Validation.ReplacementContentFlowSourceRoots
import Goose.GIR.ReplacementContentFlowProofsTouchFootprintRounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_function_native_instruction {module : Core.Module} {index : Nat} {func : Func}
    (accepted : Core.validate module = .ok ())
    (functionAt : (lower module).funcs[index]? = some func)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {instruction : Inst} (member : instruction ∈ block.insts) :
    checkInstTypes func { (lower module).tyEnv func with vals := func.valueTypes (lower module) }
      (func.valueTypes (lower module)) instruction = .ok () := by
  let info : FnInfo := ⟨s!"function {func.name}",func,func.valueTypes (lower module)⟩
  have infoMember : info ∈ (lower module).infos := by
    apply List.mem_map.mpr
    refine ⟨(s!"function {func.name}",func),?_,rfl⟩
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨func,by simpa using Array.mem_of_getElem? functionAt,rfl⟩
  exact lower_instructions_typed_of_accepted accepted infoMember blockMember member

theorem global_nonowner_summaryTouchPolicy {module : GIR.Module} {func : Func}
    (closed : storageClosed module = true) {index : GlobalId} {payload : Ty} {kind : VarKind}
    (row : (module.tyEnv func).globals[index]? = some (payload,kind))
    (interior : payload.ownerElem?.isSome = false) : summaryTouchPolicy module func (.global index) := by
  change (module.globals.map (fun global => (global.ty,global.kind)))[index]? = some (payload,kind) at row
  have globalAt : ∃ global, module.globals[index]? = some global ∧ global.ty = payload := by
    cases found : module.globals[index]? with
    | none => simp [found] at row
    | some global =>
        have same : global.ty = payload := by
          have same : (global.ty,global.kind) = (payload,kind) := by
            simpa [found] using row
          exact (Prod.mk.inj same).1
        exact ⟨global,rfl,same⟩
  obtain ⟨global,globalAt,rfl⟩ := globalAt
  have owners : ownerTouches module [.global index] = [] := by
    simp [ownerTouches,closed,globalAt,interior]
  have dependencies : ownerDependencies module func (.known [.global index]) = some [] := by
    unfold ownerDependencies
    rw [rawOwnerTouches_singleton]
    simp [owners,normalize]
  cases summaryAt : func.summary with
  | unknown => simp [summaryTouchPolicy,summaryTouchRoots,summaryAt]
  | known summary =>
      simp only [summaryTouchPolicy,summaryTouchRoots,summaryAt]
      exact ⟨[],dependencies,by simp⟩

#print axioms accepted_function_native_instruction
#print axioms global_nonowner_summaryTouchPolicy

end Goose.Lower.Validation
