import Goose.Lower.Validation.SymbolTables
import Goose.Lower.Validation.SummaryPreservationVariableShape

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem forIn_yields_member_core {items : List α}
    {body : α → Core.V (ForInStep PUnit.{1})}
    (yielded : ∀ item step, body item = .ok step → step = .yield PUnit.unit)
    (checked : forIn items PUnit.unit (fun item _ => body item) = .ok PUnit.unit) :
    ∀ item ∈ items, body item = .ok (.yield PUnit.unit) := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := (ex_bind_ok _ _ _).mp checked
    have equal := yielded item step first
    subst step
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact ih remaining next member

theorem checkAnnotationShape_row {module : Core.Module} {impl : Core.Impl} {ctx : Core.Context}
    (checked : Core.checkAnnotationShape module impl ctx = .ok ())
    {varId : VarId} {roots : List RootRef} (member : (varId, roots) ∈ ctx.varRoots) :
    ∃ localVar, impl.vars[varId]? = some localVar ∧ localVar.ty.isRefLike = true ∧
      ∀ global, .global global ∈ roots → global < module.globals.size := by
  unfold Core.checkAnnotationShape at checked
  obtain ⟨_, rows, _⟩ := (ex_bind_ok _ _ _).mp checked
  have row := forIn_yields_member_core (checked := rows) (by
    intro pair step one
    obtain ⟨index, declared⟩ := pair
    cases present : impl.vars[index]? with
    | none => simp [present, Core.reject, bind, Except.bind] at one
    | some localVar =>
      simp only [present] at one
      by_cases reference : localVar.ty.isRefLike = true
      · simp only [reference, ite_true] at one
        obtain ⟨_, _, last⟩ := (ex_bind_ok _ _ _).mp one
        simpa [pure, Except.pure] using last.symm
      · simp [reference, Core.reject, bind, Except.bind] at one) (varId, roots) member
  cases lookup : impl.vars[varId]? with
  | none => simp [lookup, Core.reject, bind, Except.bind] at row
  | some localVar =>
    simp only [lookup] at row
    inv at row
    refine ⟨localVar, rfl, row.1, ?_⟩
    intro global member
    have globalRow := forIn_yields_member_core (checked := row.2) (by
      intro root step one
      cases root <;>
        repeat' first
        | (simpa [Core.reject, pure, Except.pure, bind, Except.bind] using one.symm)
        | (split at one)) (.global global) member
    by_cases bound : global < module.globals.size
    · exact bound
    · simp [bound, Core.reject, bind, Except.bind] at globalRow

theorem checkAnnotationShape_root_bounds {module : Core.Module} {impl : Core.Impl} {ctx : Core.Context}
    (checked : Core.checkAnnotationShape module impl ctx = .ok ())
    {varId : VarId} {roots : List RootRef} (member : (varId, roots) ∈ ctx.varRoots) :
    ∀ root ∈ roots,
      match root with
      | .local index => index < impl.vars.size
      | .global index => index < module.globals.size
      | .param index => index < impl.params.size := by
  unfold Core.checkAnnotationShape at checked
  obtain ⟨_, rows, _⟩ := (ex_bind_ok _ _ _).mp checked
  have row := forIn_yields_member_core (checked := rows) (by
    intro pair step one
    obtain ⟨index, declared⟩ := pair
    cases present : impl.vars[index]? with
    | none => simp [present, Core.reject, bind, Except.bind] at one
    | some localVar =>
      simp only [present] at one
      by_cases reference : localVar.ty.isRefLike = true
      · simp only [reference, ite_true] at one
        obtain ⟨_, _, last⟩ := (ex_bind_ok _ _ _).mp one
        simpa [pure, Except.pure] using last.symm
      · simp [reference, Core.reject, bind, Except.bind] at one) (varId, roots) member
  cases lookup : impl.vars[varId]? with
  | none => simp [lookup, Core.reject, bind, Except.bind] at row
  | some localVar =>
    simp only [lookup] at row
    inv at row
    intro root rootMember
    have one := forIn_yields_member_core (checked := row.2) (by
      intro selected step one
      cases selected <;>
        repeat' first
        | (simpa [Core.reject, pure, Except.pure, bind, Except.bind] using one.symm)
        | (split at one)) root rootMember
    cases root with
    | «local» index =>
      cases target : impl.vars[index]? with
      | none => simp [target, Core.reject, bind, Except.bind] at one
      | some value => exact (Array.getElem?_eq_some_iff.mp target).1
    | global index =>
      by_cases bound : index < module.globals.size
      · exact bound
      · simp [bound, Core.reject, bind, Except.bind] at one
    | param index =>
      by_cases bound : index < impl.params.size
      · exact bound
      · simp [bound, Core.reject, bind, Except.bind] at one

theorem lowerContextRootCeiling_root_bounds {module : Core.Module} {impl : Core.Impl} {ctx : Core.Context}
    {roots : List RootRef}
    (bounded : ∀ root ∈ roots,
      match root with
      | .local index => index < impl.vars.size
      | .global index => index < module.globals.size
      | .param index => index < impl.params.size) :
    ∀ root ∈ lowerContextRootCeiling ctx impl roots,
      match root with
      | .local index => index < impl.vars.size
      | .global index => index < module.globals.size
      | .param index => index < impl.params.size := by
  intro root member
  rcases unionRoots_mem _ _ _ member with original | added
  · exact bounded root original
  · obtain ⟨⟨parameter, index⟩, atIndex, selected⟩ := List.mem_filterMap.mp added
    have lookup : impl.params[index]? = some parameter := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp atIndex
    have bound := (Array.getElem?_eq_some_iff.mp lookup).1
    simp only at selected
    cases annotation : ctx.varRoots.find? (·.1 == parameter.var) with
    | none => simp [annotation] at selected
    | some row =>
      simp only [annotation] at selected
      split at selected
      · simp only [Option.some.injEq] at selected
        subst root
        exact bound
      · simp at selected

theorem lowerContextAt_parameter_facts {module : Core.Module} {contextIndex : ContextId}
    {ctx : Core.Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl)
    (index : Nat) (roots : List RootRef)
    (member : (index, roots) ∈ (lowerContextAt module ctx impl).roots.params.toList) :
    index < (lowerContextAt module ctx impl).params.length ∧
      (lowerContextAt module ctx impl).params[index]!.isRefLike = true ∧
      ∀ root ∈ roots, RootRef.ParameterWithin (lower module) index root := by
  obtain ⟨found, foundAt, context⟩ := (validate_modOk module accepted).ctx contextIndex ctx contextAt
  rw [implAt] at foundAt
  cases foundAt
  change (index, roots) ∈ (impl.params.toList.zipIdx.filterMap fun (param, position) =>
    (ctx.varRoots.find? (·.1 == param.var)).map fun (_, roots) => (position, roots)).toArray.toList at member
  simp only at member
  obtain ⟨⟨param, position⟩, parameterMember, selected⟩ := List.mem_filterMap.mp member
  cases annotation : ctx.varRoots.find? (·.1 == param.var) with
  | none => simp [annotation] at selected
  | some row =>
    obtain ⟨varId, declared⟩ := row
    simp only [annotation, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨rfl, rfl⟩ := selected
    have identity : varId = param.var := by simpa using List.find?_some annotation
    subst varId
    have parameterAt : impl.params[position]? = some param := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    have bound : position < impl.params.size := (Array.getElem?_eq_some_iff.mp parameterAt).1
    obtain ⟨aligned, localVar, localAt, _, _⟩ :=
      (validate_modOk module accepted).impl ctx.impl impl implAt |>.params position param parameterAt
    obtain ⟨annotatedVar, annotatedAt, reference, globalBounds⟩ :=
      checkAnnotationShape_row context.annotationShape (List.mem_of_find?_eq_some annotation)
    rw [aligned, localAt] at annotatedAt
    cases annotatedAt
    have targetBound : position < (lowerContextAt module ctx impl).params.length := by
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using bound
    have targetAt : (lowerContextAt module ctx impl).params[position]? = some localVar.ty := by
      simp [lowerContextAt, lowerImpl, lowerImplFromState, List.getElem?_map, parameterAt, tyOfVar, aligned, localAt]
    have targetType : (lowerContextAt module ctx impl).params[position] = localVar.ty := by
      simpa only [List.getElem?_eq_getElem targetBound, Option.some.injEq] using targetAt
    refine ⟨targetBound, ?_, ?_⟩
    · simpa [getElem!_pos, targetBound, targetType] using reference
    · intro root rootMember
      have shape := context.paramAnn position declared bound
        (by simpa [aligned, annotation] using congrArg (Option.map Prod.snd) annotation)
        root rootMember
      rcases shape with rfl | ⟨global, rfl⟩
      · rfl
      · simpa [RootRef.ParameterWithin, lower] using globalBounds global rootMember

theorem checkContentShape_row {module : Core.Module} {impl : Core.Impl} {ctx : Core.Context}
    (checked : Core.checkContentShape module impl ctx = .ok ())
    {varId : VarId} {roots : List RootRef} (member : (varId, roots) ∈ ctx.contentRoots) :
    varId < impl.params.size ∧ ∃ localVar, impl.vars[varId]? = some localVar ∧
      localVar.ty.isRefSlice = true ∧ ∀ root ∈ roots,
        match root with
        | .local _ => False
        | .global index => index < module.globals.size
        | .param index => index < impl.params.size := by
  unfold Core.checkContentShape at checked
  have row := (forAll_ok _ _).mp checked (varId, roots) member
  inv at row
  refine ⟨row.1, ?_⟩
  have typed := row.2
  cases lookup : impl.vars[varId]? with
  | none => simp [lookup, Core.reject] at typed
  | some localVar =>
    simp only [lookup] at typed
    inv at typed
    obtain ⟨slice, _, allRoots⟩ := typed
    refine ⟨localVar, rfl, slice, ?_⟩
    intro root member
    have one := (forAll_ok _ _).mp allRoots root member
    cases root with
    | «local» index => simp [Core.reject] at one
    | global index =>
      by_cases bound : index < module.globals.size
      · exact bound
      · simp [bound, Core.reject] at one
    | param index =>
      by_cases bound : index < impl.params.size
      · exact bound
      · simp [bound, Core.reject] at one

theorem lowerContextAt_content_facts {module : Core.Module} {contextIndex : ContextId}
    {ctx : Core.Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl)
    (index : Nat) (roots : List RootRef)
    (member : (index, roots) ∈ (lowerContextAt module ctx impl).roots.contents.toList) :
    index < (lowerContextAt module ctx impl).params.length ∧
      (lowerContextAt module ctx impl).params[index]!.isRefSlice = true ∧
      ∀ root ∈ roots, RootRef.ExternalWithin (lower module) (lowerContextAt module ctx impl) root := by
  obtain ⟨found, foundAt, context⟩ := (validate_modOk module accepted).ctx contextIndex ctx contextAt
  rw [implAt] at foundAt
  cases foundAt
  change (index, roots) ∈ (impl.params.toList.zipIdx.filterMap fun (param, position) =>
    (ctx.contentRoots.find? (·.1 == param.var)).map fun (_, roots) => (position, roots)).toArray.toList at member
  simp only at member
  obtain ⟨⟨param, position⟩, parameterMember, selected⟩ := List.mem_filterMap.mp member
  cases annotation : ctx.contentRoots.find? (·.1 == param.var) with
  | none => simp [annotation] at selected
  | some row =>
    obtain ⟨varId, declared⟩ := row
    simp only [annotation, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨rfl, rfl⟩ := selected
    have identity : varId = param.var := by simpa using List.find?_some annotation
    subst varId
    have parameterAt : impl.params[position]? = some param := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    have bound : position < impl.params.size := (Array.getElem?_eq_some_iff.mp parameterAt).1
    obtain ⟨aligned, localVar, localAt, _, _⟩ :=
      (validate_modOk module accepted).impl ctx.impl impl implAt |>.params position param parameterAt
    obtain ⟨_, annotatedVar, annotatedAt, reference, rootBounds⟩ :=
      checkContentShape_row context.contentShape (List.mem_of_find?_eq_some annotation)
    rw [aligned, localAt] at annotatedAt
    cases annotatedAt
    have targetBound : position < (lowerContextAt module ctx impl).params.length := by
      simpa [lowerContextAt, lowerImpl, lowerImplFromState] using bound
    have targetAt : (lowerContextAt module ctx impl).params[position]? = some localVar.ty := by
      simp [lowerContextAt, lowerImpl, lowerImplFromState, List.getElem?_map, parameterAt, tyOfVar, aligned, localAt]
    have targetType : (lowerContextAt module ctx impl).params[position] = localVar.ty := by
      simpa only [List.getElem?_eq_getElem targetBound, Option.some.injEq] using targetAt
    refine ⟨targetBound, ?_, ?_⟩
    · simpa [getElem!_pos, targetBound, targetType] using reference
    · intro root rootMember
      have bound := rootBounds root rootMember
      cases root <;>
        simpa [RootRef.ExternalWithin, lower, lowerContextAt, lowerImpl, lowerImplFromState] using bound

theorem checkResultShape_roots {module : Core.Module} {impl : Core.Impl} {ctx : Core.Context}
    (checked : Core.checkResultShape module impl ctx = .ok ()) :
    ∀ roots ∈ ctx.resultRoots, ∀ root ∈ roots,
      match root with
      | .local _ => False
      | .global index => index < module.globals.size
      | .param index => index < impl.params.size := by
  have length := checkResultShape_size checked
  unfold Core.checkResultShape at checked
  inv at checked
  intro roots member root rootMember
  obtain ⟨index, rootsAt⟩ := List.mem_iff_getElem?.mp member
  have indexBound : index < impl.results.size := by
    have bound := (List.getElem?_eq_some_iff.mp rootsAt).1
    omega
  have pairMember : (impl.results[index], roots) ∈ impl.results.toList.zip ctx.resultRoots := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨index, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨by simp [indexBound], rootsAt⟩
  have row := forIn_yields_member_core (checked := checked.2) (by
    intro pair step one
    by_cases invalid : (!pair.1.isRefLike && !pair.2.isEmpty) = true
    · simp [invalid, Core.reject, bind, Except.bind] at one
    · simp only [invalid, ite_false] at one
      obtain ⟨_, _, last⟩ := (ex_bind_ok _ _ _).mp one
      simpa [pure, Except.pure] using last.symm) _ pairMember
  by_cases invalid : (!(impl.results[index]).isRefLike && !roots.isEmpty) = true
  · simp [invalid, Core.reject, bind, Except.bind] at row
  · simp only [invalid, ite_false] at row
    obtain ⟨_, rootLoop, _⟩ := (ex_bind_ok _ _ _).mp row
    have one := forIn_yields_member_core (checked := rootLoop) (by
      intro current step accepted
      cases current <;>
        repeat' first
        | (simpa [Core.reject, pure, Except.pure, bind, Except.bind] using accepted.symm)
        | (split at accepted)) root rootMember
    cases root with
    | «local» index => simp [Core.reject, bind, Except.bind] at one
    | global index =>
      by_cases bound : index < module.globals.size
      · exact bound
      · simp [bound, Core.reject, bind, Except.bind] at one
    | param index =>
      by_cases bound : index < impl.params.size
      · exact bound
      · cases lookup : impl.vars[index]? <;>
          simp [lookup, bound, Core.reject, bind, Except.bind] at one

theorem lowerContextAt_result_facts {module : Core.Module} {contextIndex : ContextId}
    {ctx : Core.Context} {impl : Core.Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl)
    (roots : List RootRef) (member : roots ∈ (lowerContextAt module ctx impl).roots.results.toList) :
    ∀ root ∈ roots, RootRef.ExternalWithin (lower module) (lowerContextAt module ctx impl) root := by
  obtain ⟨found, foundAt, context⟩ := (validate_modOk module accepted).ctx contextIndex ctx contextAt
  rw [implAt] at foundAt
  cases foundAt
  change roots ∈ ((List.range impl.results.size).map fun index =>
    let declared := ctx.resultRoots[index]?.getD []
    let parameters := impl.params.toList.zipIdx.filterMap fun (param, position) =>
      match ctx.varRoots.find? (·.1 == param.var) with
      | some (_, parameterRoots) =>
        if parameterRoots.all declared.contains then some (.param position) else none
      | none => none
    unionRoots declared parameters).toArray.toList at member
  simp only at member
  obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
  intro root member
  rcases unionRoots_mem _ _ root member with declared | parameter
  · cases row : ctx.resultRoots[index]? with
    | none => simp [row] at declared
    | some roots =>
      simp only [row, Option.getD_some] at declared
      have bound := checkResultShape_roots context.resultShape roots
        (List.mem_of_getElem? row) root declared
      cases root <;>
        simpa [RootRef.ExternalWithin, lower, lowerContextAt, lowerImpl, lowerImplFromState] using bound
  · obtain ⟨⟨param, position⟩, parameterMember, selected⟩ := List.mem_filterMap.mp parameter
    have parameterAt := List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    have bound : position < impl.params.size := by
      simpa only [Array.length_toList] using (List.getElem?_eq_some_iff.mp parameterAt).1
    cases annotation : ctx.varRoots.find? (·.1 == param.var) with
    | none => simp [annotation] at selected
    | some row =>
      obtain ⟨varId, parameterRoots⟩ := row
      simp only [annotation] at selected
      split at selected
      · have equal : RootRef.param position = root := Option.some.inj selected
        subst root
        simpa [RootRef.ExternalWithin, lowerContextAt, lowerImpl, lowerImplFromState] using bound
      · cases selected

end Goose.Lower.Validation
