import Goose.Lower.Validation.ReplacementContentFlowSourceShape
import Goose.Lower.Validation.SymbolSourceTables

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem selected_keys_nodup {α β : Type} (items : List α) (select : α → Option β) :
    ((items.zipIdx.filterMap fun (item, index) => (select item).map (index, ·)).map (·.1)).Nodup := by
  change List.Pairwise (· ≠ ·) _
  rw [List.pairwise_map]
  have distinct : List.Pairwise (fun left right : α × Nat => left.2 ≠ right.2) items.zipIdx := by
    rw [← List.pairwise_map]
    simp only [List.zipIdx_map_snd]
    exact List.nodup_range' 1
  apply distinct.filterMap _
  intro left right different outLeft leftSelected outRight rightSelected
  cases first : select left.1 with
  | none => simp [first] at leftSelected
  | some firstValue =>
    simp only [first, Option.map_some, Option.some.injEq] at leftSelected
    cases leftSelected
    cases second : select right.1 with
    | none => simp [second] at rightSelected
    | some secondValue =>
      simp only [second, Option.map_some, Option.some.injEq] at rightSelected
      cases rightSelected
      exact different

private theorem eraseDups_of_nodup {items : List Nat} (unique : items.Nodup) :
    items.eraseDups = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨absent, rest⟩ := List.nodup_cons.mp unique
    rw [List.eraseDups_cons]
    have unchanged : tail.filter (fun item => !item == head) = tail := by
      apply List.filter_eq_self.mpr
      intro item member
      have different : item ≠ head := by
        intro same
        subst item
        exact absent member
      simp [different]
    rw [unchanged, ih rest]

private theorem annotationsValid_of_tables {module : GIR.Module} {func : Func}
    (tables : SymbolTableFacts module func)
    (parametersUnique : (func.roots.params.toList.map (·.1)).Nodup)
    (contentsUnique : (func.roots.contents.toList.map (·.1)).Nodup) :
    annotationsValid module func = true := by
  simp only [annotationsValid, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [eraseDups_of_nodup parametersUnique, List.length_map]
  · rw [eraseDups_of_nodup contentsUnique, List.length_map]
  · apply List.all_eq_true.mpr
    rintro ⟨index, roots⟩ member
    obtain ⟨bound, reference, rootBounds⟩ := tables.parameters index roots member
    rw [Bool.and_eq_true]
    constructor
    · rw [List.getElem?_eq_getElem bound]
      simpa only [Option.any_some, getElem!_pos func.params index bound] using reference
    · apply List.all_eq_true.mpr
      intro root rootMember
      have known := rootBounds root rootMember
      cases root with
      | «local» slot => exact False.elim known
      | global global => simpa [RootRef.ParameterWithin] using known
      | param parameter =>
        change parameter = index at known
        subst parameter
        simp [bound]
  · apply List.all_eq_true.mpr
    rintro ⟨index, roots⟩ member
    obtain ⟨bound, reference, rootBounds⟩ := tables.contents index roots member
    rw [Bool.and_eq_true]
    constructor
    · rw [List.getElem?_eq_getElem bound]
      simpa only [Option.any_some, getElem!_pos func.params index bound] using reference
    · apply List.all_eq_true.mpr
      intro root rootMember
      have known := rootBounds root rootMember
      cases root <;> simpa only [RootRef.ExternalWithin, decide_eq_true_eq] using known
  · apply Array.all_eq_true_iff_forall_mem.mpr
    intro roots member
    apply List.all_eq_true.mpr
    intro root rootMember
    have known := tables.results roots (Array.mem_toList_iff.mpr member) root rootMember
    cases root <;> simpa only [RootRef.ExternalWithin, decide_eq_true_eq] using known

theorem accepted_context_annotationsValid {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    annotationsValid (lower module) (lowerContextAt module ctx impl) = true := by
  apply annotationsValid_of_tables (lowerContextAt_symbol_tables accepted contextRow implementationRow)
  · change ((lowerContextRootInfo ctx impl).params.toList.map (·.1)).Nodup
    simpa only [lowerContextRootInfo, List.toList_toArray, Option.map_map, Function.comp_def] using
      selected_keys_nodup impl.params.toList
        (fun parameter => (ctx.varRoots.find? (·.1 == parameter.var)).map (·.2))
  · change ((lowerContextRootInfo ctx impl).contents.toList.map (·.1)).Nodup
    simpa only [lowerContextRootInfo, List.toList_toArray, Option.map_map, Function.comp_def] using
      selected_keys_nodup impl.params.toList
        (fun parameter => (ctx.contentRoots.find? (·.1 == parameter.var)).map (·.2))

theorem accepted_global_annotationsValid {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    annotationsValid (lower module) (lowerGlobal module global).init = true := by
  apply annotationsValid_of_tables (lowerGlobal_symbol_tables accepted globalRow)
  · simp [lowerGlobal]
  · simp [lowerGlobal]

theorem accepted_function_annotationsValid {module : Core.Module} {index : FnId} {func : Func}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func) :
    annotationsValid (lower module) func = true := by
  obtain ⟨ctx, impl, contextRow, implementationRow, rfl⟩ :=
    accepted_function_context accepted functionRow
  exact accepted_context_annotationsValid accepted contextRow implementationRow

theorem accepted_initializer_annotationsValid {module : Core.Module} {index : GlobalId}
    {global : GIR.Global} (accepted : Core.validate module = .ok ())
    (globalRow : (lower module).globals[index]? = some global) :
    annotationsValid (lower module) global.init = true := by
  cases sourceRow : module.globals[index]? with
  | none => simp [lower, Array.getElem?_map, sourceRow] at globalRow
  | some source =>
    have identity : global = lowerGlobal module source := by
      simpa only [lower, Array.getElem?_map, sourceRow, Option.map_some, Option.some.injEq] using globalRow.symm
    rw [identity]
    exact accepted_global_annotationsValid accepted sourceRow

#print axioms accepted_function_annotationsValid
#print axioms accepted_initializer_annotationsValid
#print axioms accepted_context_annotationsValid
#print axioms accepted_global_annotationsValid

end Goose.Lower.Validation.ReplacementContentFlowSource
