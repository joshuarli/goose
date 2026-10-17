import Goose.Lower.Validation.CfgFunctionUnreachable

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem forIn_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item ∈ items, body item () = .ok (.yield ())) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem forIn'_ok {items : List α}
    {body : (item : α) → item ∈ items → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item member, body item member () = .ok (.yield ())) :
    forIn' items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn'_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem loop_done {loop : Check PUnit} {value : α}
    (checked : loop = .ok ()) : (loop >>= fun _ => pure value) = .ok value := by
  simp [checked, bind, Except.bind, pure, Except.pure]

theorem FunctionUnreachable.checked {noReturn : ContextId → Bool} {func : Func}
    (code : FunctionUnreachable noReturn func) (mayReturn : Array Bool)
    (callees : ∀ callee, noReturn callee = true → mayReturn[callee]?.getD true = false)
    (label : String) : checkUnreachableOf mayReturn label func = .ok () := by
  unfold checkUnreachableOf
  apply loop_done
  rw [← Array.forIn_toList]
  apply forIn_ok
  intro block member
  apply loop_done
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply forIn'_ok
  intro index present
  have bound : index < block.insts.length := by
    simpa [Std.Legacy.Range.size, List.mem_range'] using present
  cases found : block.insts[index] with
  | «def» value op => simp [pure, Except.pure]
  | eff effect => simp [pure, Except.pure]
  | term term =>
    cases term <;> try simp [pure, Except.pure]
    obtain ⟨value, callee, args, origin, previous, stops⟩ :=
      (code block member).paired index (by simpa [found] using List.getElem?_eq_getElem bound)
    simp [previous, callees callee stops]

theorem lowerImpl_checkUnreachableOf (module : Core.Module) (impl : Core.Impl)
    (mayReturn : Array Bool)
    (callees : ∀ callee, module.noReturn callee = true → mayReturn[callee]?.getD true = false)
    (label : String) : checkUnreachableOf mayReturn label (lowerImpl module impl) = .ok () :=
  (lowerImpl_unreachableCode module impl).checked mayReturn callees label

theorem lowerGlobal_checkUnreachableOf (module : Core.Module) (global : Core.Global)
    (mayReturn : Array Bool)
    (callees : ∀ callee, module.noReturn callee = true → mayReturn[callee]?.getD true = false)
    (label : String) : checkUnreachableOf mayReturn label (lowerGlobal module global).init = .ok () :=
  (lowerGlobal_unreachableCode module global).checked mayReturn callees label

private theorem checkAll_ok {items : List α} {action : α → Except ε Unit}
    (accepted : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [checkAll, accepted item (by simp), bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

theorem lower_checkUnreachable (module : Core.Module)
    (callees : ∀ callee, module.noReturn callee = true →
      (lower module).functionsMayReturn[callee]?.getD true = false) :
    checkUnreachable (lower module) = .ok () := by
  unfold checkUnreachable
  apply checkAll_ok
  intro pair member
  apply (lower_unreachableCode module pair.2 ?_).checked _ callees pair.1
  unfold GIR.Module.labelled at member
  rcases List.mem_append.mp member with implementation | initializer
  · obtain ⟨func, present, same⟩ := List.mem_map.mp implementation
    exact List.mem_append_left _ (same ▸ present)
  · obtain ⟨global, present, same⟩ := List.mem_map.mp initializer
    have initMember : global.init ∈ (lower module).globals.toList.map (·.init) :=
      List.mem_map.mpr ⟨global, present, rfl⟩
    exact List.mem_append_right _ (same ▸ initMember)

end Goose.Lower.Validation
