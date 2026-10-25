import Goose.Lower.Validation.ReplacementCallSummaryRoots

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation

theorem ReplacementDemandContext.call_effect_owner_root_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {function : ContextId} {arguments : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call function arguments callOrigin)))
    {target : DemandOwner} {effects : List DemandOwner}
    (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (effectsAt : demand.planContext.approvals.access.callEffectOwners function arguments = .ok effects)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {root : RootRef} (member : root ∈ effects.flatMap DemandOwner.roots) :
    ReplacementApart queries owner (some (func.expandParameterRoot root)) := by
  apply demand.descendant_call_query_apart source targetAt effectsAt closed ownerKnown
  refine ⟨func.expandParameterRoot root, rfl, ?_⟩
  intro expanded expandedAt
  exact List.mem_flatMap.mpr ⟨root, member, expandedAt⟩

theorem callEffectOwners_known_roots {access : AccessEnv} {function : ContextId}
    {context : Context} {impl : Impl} {arguments : List Arg} {summary : Core.Summary}
    {effects : List DemandOwner}
    (contextAt : access.mod.contexts[function]? = some context)
    (implAt : access.mod.impls[context.impl]? = some impl)
    (summaryAt : impl.summary = .known summary)
    (checked : access.callEffectOwners function arguments = .ok effects) :
    ∃ actual, access.argsRoots arguments = .ok actual ∧
      effects.flatMap DemandOwner.roots =
        (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds).flatMap (fun
          | .global global => [RootRef.global global]
          | .param index => actual[index]?.getD [] ++ (paramGlobals impl context index).filterMap (fun
            | .global global => some (RootRef.global global) | _ => none)) := by
  unfold AccessEnv.callEffectOwners at checked
  simp only [contextAt, implAt] at checked
  obtain ⟨actual, actualAt, checked⟩ := (ex_bind_ok _ _ _).mp checked
  refine ⟨actual, actualAt, ?_⟩
  exact targetOwners_roots (by simpa only [summaryAt] using checked)

theorem callEffectOwners_known_global {access : AccessEnv} {function : ContextId}
    {context : Context} {impl : Impl} {arguments : List Arg} {summary : Core.Summary}
    {effects : List DemandOwner}
    (contextAt : access.mod.contexts[function]? = some context)
    (implAt : access.mod.impls[context.impl]? = some impl)
    (summaryAt : impl.summary = .known summary)
    (checked : access.callEffectOwners function arguments = .ok effects)
    {global : GlobalId}
    (member : Target.global global ∈ summary.reads ++ summary.writes ++ summary.grows ++
      summary.shrinks ++ summary.rebinds) :
    RootRef.global global ∈ effects.flatMap DemandOwner.roots := by
  obtain ⟨actual, _, rootsEq⟩ := callEffectOwners_known_roots contextAt implAt summaryAt checked
  rw [rootsEq]
  exact List.mem_flatMap.mpr ⟨Target.global global, member, by simp⟩

theorem callEffectOwners_known_parameter_global {access : AccessEnv} {function : ContextId}
    {context : Context} {impl : Impl} {arguments : List Arg} {summary : Core.Summary}
    {effects : List DemandOwner}
    (contextAt : access.mod.contexts[function]? = some context)
    (implAt : access.mod.impls[context.impl]? = some impl)
    (summaryAt : impl.summary = .known summary)
    (checked : access.callEffectOwners function arguments = .ok effects)
    {index : Nat} (member : Target.param index ∈ summary.reads ++ summary.writes ++ summary.grows ++
      summary.shrinks ++ summary.rebinds) {global : GlobalId}
    (globalMember : Target.global global ∈ paramGlobals impl context index) :
    RootRef.global global ∈ effects.flatMap DemandOwner.roots := by
  obtain ⟨actual, _, rootsEq⟩ := callEffectOwners_known_roots contextAt implAt summaryAt checked
  rw [rootsEq]
  apply List.mem_flatMap.mpr
  refine ⟨Target.param index, member, List.mem_append_right _ ?_⟩
  exact List.mem_filterMap.mpr ⟨Target.global global, globalMember, rfl⟩

theorem callEffectOwners_known_expanded_global {access : AccessEnv} {function : ContextId}
    {context : Context} {impl : Impl} {arguments : List Arg} {summary : Core.Summary}
    {effects : List DemandOwner}
    (contextAt : access.mod.contexts[function]? = some context)
    (implAt : access.mod.impls[context.impl]? = some impl)
    (summaryAt : impl.summary = .known summary)
    (checked : access.callEffectOwners function arguments = .ok effects)
    {global : GlobalId}
    (expanded : Target.global global ∈ expandTargets impl context
      (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)) :
    RootRef.global global ∈ effects.flatMap DemandOwner.roots := by
  obtain ⟨target, targetMember, expanded⟩ := List.mem_flatMap.mp expanded
  cases target with
  | global index =>
    have same : global = index := by simpa using expanded
    subst index
    exact callEffectOwners_known_global contextAt implAt summaryAt checked targetMember
  | param index =>
    apply callEffectOwners_known_parameter_global contextAt implAt summaryAt checked targetMember
    cases variableAt : impl.vars[index]? with
    | none => simp [variableAt] at expanded
    | some localVar =>
      cases annotationAt : context.varRoots.find? (·.1 == index) with
      | none => simp [variableAt, annotationAt] at expanded
      | some annotation =>
        by_cases reference : localVar.ty.isRefLike = true
        · simp only [variableAt, annotationAt, reference, ↓reduceIte] at expanded
          obtain ⟨root, rootMember, mapped⟩ := List.mem_filterMap.mp expanded
          cases root with
          | «local» slot => simp [rootTarget] at mapped
          | param parameter => simp [rootTarget] at mapped
          | global other =>
            have same : other = global := by simpa [rootTarget] using mapped
            subst other
            simp only [paramGlobals, variableAt, annotationAt, reference, ↓reduceIte]
            exact List.mem_filterMap.mpr ⟨RootRef.global global, rootMember, rfl⟩
        · simp [variableAt, annotationAt, reference] at expanded

theorem callEffectOwners_unknown_global {access : AccessEnv} {function : ContextId}
    {context : Context} {impl : Impl} {arguments : List Arg} {effects : List DemandOwner}
    (contextAt : access.mod.contexts[function]? = some context)
    (implAt : access.mod.impls[context.impl]? = some impl)
    (summaryAt : impl.summary = .unknown)
    (checked : access.callEffectOwners function arguments = .ok effects)
    {global : GlobalId} {declaration : Core.Global}
    (globalAt : access.mod.globals[global]? = some declaration)
    (owning : declaration.ty.ownerElem?.isSome = true) :
    RootRef.global global ∈ effects.flatMap DemandOwner.roots := by
  unfold AccessEnv.callEffectOwners at checked
  simp only [contextAt, implAt] at checked
  obtain ⟨actual, _, checked⟩ := (ex_bind_ok _ _ _).mp checked
  have equal : effects = access.unknownOwners actual := by
    simpa only [summaryAt, pure, Except.pure, Except.ok.injEq] using checked.symm
  rw [equal]
  apply List.mem_flatMap.mpr
  refine ⟨⟨some declaration.ty, [.global global]⟩, ?_, by simp⟩
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  refine ⟨(declaration, global), ?_, ?_⟩
  · apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [Array.getElem?_toList] using globalAt
  · simp [owning]

#print axioms ReplacementDemandContext.call_effect_owner_root_apart
#print axioms callEffectOwners_known_roots
#print axioms callEffectOwners_known_global
#print axioms callEffectOwners_known_parameter_global
#print axioms callEffectOwners_known_expanded_global
#print axioms callEffectOwners_unknown_global

end Goose.Lower.Validation
