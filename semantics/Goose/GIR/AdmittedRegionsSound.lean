import Goose.GIR.AdmittedRegions

namespace Goose.GIR

open Goose.Core

theorem Func.checkAdmittedRegions_return {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {values : List ValueId} {org : Option OriginId}
    (returned : Inst.term (.ret values org) ∈ block.insts)
    {value index : Nat} (operand : (value,index) ∈ values.zipIdx)
    (reference : valRefLike vt value = true) :
    ∀ root ∈ rootsAt p.vals value, root ∈ f.roots.results[index]?.getD [] := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember returned
  change values.zipIdx.all _ = true at instruction
  have bound := List.all_eq_true.mp instruction (value,index) operand
  simp only [reference, Bool.not_true, Bool.false_or] at bound
  simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound

theorem Func.checkAdmittedRegions_call {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {value fn : Nat} {args : List ValueId} {org : Option OriginId}
    (called : Inst.def value (.call fn args org) ∈ block.insts)
    {callee : Func} (calleeAt : m.funcs[fn]? = some callee)
    {parameter : Nat} {ceiling : List RootRef} (row : (parameter,ceiling) ∈ callee.roots.contents.toList)
    (reference : (callee.params[parameter]?).any Ty.isRefSlice = true) :
    (∀ root ∈ argumentContents f p args[parameter]!, root ∈ mapContentRoots f p args ceiling) ∧
    (∀ root ∈ mapContentRoots f p args ceiling, root ∈ argumentContents f p args[parameter]!) := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember called
  simp only [Func.admittedInstruction, calleeAt] at instruction
  have bound := List.all_eq_true.mp instruction (parameter,ceiling) row
  simp only [reference, Bool.not_true, Bool.false_or, Bool.and_eq_true] at bound
  constructor
  · simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound.1
  · simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound.2

theorem Func.checkAdmittedRegions_store {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {address value : Nat} {org : Option OriginId}
    (stored : Inst.eff (.store address value org) ∈ block.insts)
    (reference : valRefLike vt value = true) {parameter : Nat}
    (target : RootRef.param parameter ∈ rootsAt p.vals address)
    (sliceReference : (f.params[parameter]?).any Ty.isRefSlice = true) :
    ∃ ceiling, f.roots.contents.find? (·.1 == parameter) = some (parameter,ceiling) ∧
      ∀ root ∈ (rootsAt p.vals value).flatMap f.expandParameterRoot,
        root ∈ ceiling.flatMap f.expandParameterRoot := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember stored
  simp only [Func.admittedInstruction, reference, Bool.not_true, Bool.false_or] at instruction
  have bound := List.all_eq_true.mp instruction (.param parameter) target
  simp only [sliceReference, Bool.not_true, Bool.false_or] at bound
  cases found : f.roots.contents.find? (·.1 == parameter) with
  | none => simp [found] at bound
  | some row =>
    simp only [found, Option.any_some] at bound
    have identity := Array.find?_some found
    have same : row.1 = parameter := by simpa only [beq_iff_eq] using identity
    rcases row with ⟨selected, ceiling⟩
    change selected = parameter at same
    subst selected
    refine ⟨ceiling, rfl, ?_⟩
    simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound

end Goose.GIR
