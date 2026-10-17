import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, checked item (by simp)]
    exact ih (fun next member => checked next (by simp [member]))

private theorem forIn_result_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (result : β) (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    (forIn items PUnit.unit body >>= fun _ => pure result : Check β) = .ok result := by
  rw [forIn_unit_ok checked]
  rfl

private theorem forIn'_result_ok {items : List α}
    {body : (item : α) → item ∈ items → PUnit → Check (ForInStep PUnit)}
    (result : β) (checked : ∀ item member, body item member PUnit.unit = .ok (.yield PUnit.unit)) :
    (forIn' items PUnit.unit body >>= fun _ => pure result : Check β) = .ok result := by
  have all : forIn' items PUnit.unit body = .ok PUnit.unit := by
    induction items with
    | nil => rfl
    | cons item rest ih =>
      rw [List.forIn'_cons, checked item (by simp)]
      exact ih (fun next member => checked next (by simp [member]))
  rw [all]
  rfl

private theorem bind_success {action : Check α} {next : α → Check β} {value : α} {result : β}
    (first : action = .ok value) (remaining : next value = .ok result) :
    (action >>= next) = .ok result := by
  rw [first]
  exact remaining

theorem checkRootAnnotationsOf_of_bounds {module : GIR.Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)}
    {rootCount index : Nat} {func : Func}
    (functionAt : module.funcs[index]? = some func)
    (returned : rootsAt results index ⊆ (func.roots.results[0]?).getD [])
    (parameters : let provenance := func.provenance results (types[index]?.getD #[]) rootCount
      ∀ block ∈ func.blocks.toList, ∀ value fn args origin,
        Inst.def value (.call fn args origin) ∈ block.insts →
        ∀ callee, module.funcs[fn]? = some callee → ∀ parameter (bound : parameter < callee.params.length),
          callee.params[parameter].isRefLike = true →
          (((callee.roots.params.find? (·.1 == parameter)).map (·.2) |>.getD []).contains (.param parameter) ||
            (mapArgumentRoots func provenance args[parameter]! parameter).all
              (((callee.roots.params.find? (·.1 == parameter)).map (·.2)).getD []).contains) = true)
    (contents : let provenance := func.provenance results (types[index]?.getD #[]) rootCount
      ∀ block ∈ func.blocks.toList, ∀ value fn args origin,
        Inst.def value (.call fn args origin) ∈ block.insts →
        ∀ callee, module.funcs[fn]? = some callee → ∀ parameter (bound : parameter < callee.params.length),
          callee.params[parameter].isRefSlice = true →
          ∀ row, callee.roots.contents.find? (·.1 == parameter) = some row →
            argumentContents func provenance args[parameter]! ⊆ mapContentRoots func provenance args row.2)
    (loads : let provenance := func.provenance results (types[index]?.getD #[]) rootCount
      ∀ block ∈ func.blocks.toList, ∀ value address, Inst.def value (.load address) ∈ block.insts →
        ∀ mutability element,
          (types[index]?.getD #[])[value]? = some (some (.data (.slice mutability element))) →
          ∀ parameter, RootRef.param parameter ∈ rootsAt provenance.vals address →
            (func.params[parameter]?).any Ty.isRefSlice = true →
            (func.roots.contents.find? (·.1 == parameter)).isSome = true) :
    checkRootAnnotationsOf module types results rootCount index = .ok () := by
  unfold checkRootAnnotationsOf
  simp only [functionAt]
  split
  all_goals
    try
      apply bind_success (value := PUnit.unit)
      case first =>
        apply forIn_unit_ok
        intro root member
        have present := returned member
        simp [present, pure, Except.pure]
  all_goals
    rw [← Array.forIn_toList]
    apply forIn_result_ok
    intro block blockMember
    apply forIn_result_ok
    intro inst instMember
    cases inst with
    | eff effect => rfl
    | term term => rfl
    | «def» value op =>
      cases op <;> simp only <;> try rfl
      case call fn args origin =>
        cases calleeAt : module.funcs[fn]? with
        | none => simp [calleeAt, pure, Except.pure]
        | some callee =>
          simp only [calleeAt, Std.Legacy.Range.forIn'_eq_forIn'_range']
          apply forIn'_result_ok
          intro parameter member
          have bound := (Std.Legacy.Range.mem_of_mem_range'
            (r := {start := 0, stop := callee.params.length, step := 1, step_pos := by decide}) member).2.1
          by_cases reference : callee.params[parameter].isRefLike = true
          · have allowed := parameters block blockMember value fn args origin instMember callee calleeAt
              parameter bound reference
            simp only [reference, ite_true, allowed, Bool.true_eq_false, ↓reduceIte,
              pure, Except.pure, bind, Except.bind]
            by_cases slice : callee.params[parameter].isRefSlice = true
            · simp only [slice, ite_true]
              cases found : callee.roots.contents.find? (·.1 == parameter) with
              | none => simp [found, pure, Except.pure]
              | some row =>
                have covered := contents block blockMember value fn args origin instMember callee calleeAt
                  parameter bound slice row found
                have valid : (argumentContents func
                    (func.provenance results (types[index]?.getD #[]) rootCount) args[parameter]!).all
                    (mapContentRoots func (func.provenance results (types[index]?.getD #[]) rootCount)
                      args row.2).contains = true :=
                  List.all_eq_true.mpr fun root present => List.contains_iff_mem.mpr (covered present)
                cases row
                simp only [valid, Bool.true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind]
            · simp [slice, pure, Except.pure]
          · have notSlice : callee.params[parameter].isRefSlice = false := by
              cases actual : callee.params[parameter] <;> simp [actual, Ty.isRefLike, Ty.isRefSlice] at reference ⊢
            simp [reference, notSlice, pure, Except.pure]
      case load address =>
        split <;> try rfl
        rename_i mutability element typed
        apply forIn_result_ok
        intro root member
        cases root with
        | «local» slot => rfl
        | «global» global => rfl
        | param parameter =>
          by_cases reference : (func.params[parameter]?).any Ty.isRefSlice = true
          · have observed := loads block blockMember value address instMember
              mutability element typed parameter member reference
            have present : (func.roots.contents.find? (·.1 == parameter)).isNone = false := by
              cases found : func.roots.contents.find? (·.1 == parameter) <;> simp_all
            simp [reference, present, pure, Except.pure]
          · simp [reference, pure, Except.pure]

end Goose.Lower.Validation
