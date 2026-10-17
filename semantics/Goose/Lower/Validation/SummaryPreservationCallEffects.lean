import Goose.Lower.Validation.SummaryPreservationEffectFold

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem mem_union_singletons_fold {roots initial : List RootRef} {root : RootRef} :
    root ∈ roots.foldl (fun acc item => unionRoots acc [item]) initial ↔
      root ∈ initial ∨ root ∈ roots := by
  induction roots generalizing initial with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, mem_unionRoots_iff, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc]

theorem expandedArgumentTargets_below (func : Func) (roots : List RootRef) :
    ∀ target ∈ rootsTargets ((roots.flatMap func.expandParameterRoot).foldl
      (fun acc root => unionRoots acc [root]) []),
      target ∈ func.storageTargets (rootsTargets roots) := by
  intro target member
  rw [storageTargets_rootsTargets]
  obtain ⟨root, rootMember, mapped⟩ := List.mem_filterMap.mp member
  have expanded : root ∈ roots.flatMap func.expandParameterRoot := by
    simpa only [mem_union_singletons_fold, List.not_mem_nil, false_or] using rootMember
  exact List.mem_filterMap.mpr ⟨root, expanded, mapped⟩

theorem expandedArgumentTargets_represent {func : Func} {actual source : List RootRef}
    (closed : ParameterRootsClosed func) (represented : RootsRepresent func actual source) :
    ∀ target ∈ func.storageTargets (rootsTargets ((actual.flatMap func.expandParameterRoot).foldl
      (fun acc root => unionRoots acc [root]) [])), target ∈ rootsTargets source := by
  intro target member
  exact rootsRepresent_targets represented target (storageTargets_idempotent closed target
    (storageTargets_mono (expandedArgumentTargets_below func actual) target member))

theorem storageTargets_append (func : Func) (left right : List Target) :
    func.storageTargets (left ++ right) = func.storageTargets left ++ func.storageTargets right := by
  simp only [Func.storageTargets, List.flatMap_append]

theorem mapSummaryTargets_storage_below {func : Func}
    {actual source : List (List RootRef)}
    (arguments : ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets (actual[index]?.getD [])) →
        target ∈ rootsTargets (source[index]?.getD [])) (targets : List Target) :
    ∀ target ∈ func.storageTargets (mapSummaryTargets actual targets),
      target ∈ mapSummaryTargets source targets := by
  induction targets with
  | nil => simp [mapSummaryTargets, Func.storageTargets]
  | cons head rest ih =>
    intro target member
    cases head with
    | global global =>
      change target ∈ [.global global] ++ func.storageTargets (mapSummaryTargets actual rest) at member
      change target ∈ .global global :: mapSummaryTargets source rest
      rcases List.mem_append.mp member with same | prior
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp same))
      · exact List.mem_cons_of_mem _ (ih target prior)
    | param index =>
      rw [mapSummaryTargets, storageTargets_append] at member
      rcases List.mem_append.mp member with argument | prior
      · exact List.mem_append.mpr (Or.inl (arguments index target argument))
      · exact List.mem_append.mpr (Or.inr (ih target prior))


theorem lowerContextAt_parameterGlobals {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} {param : Param} (implOk : Core.Sound.ImplOk module impl)
    (parameter : impl.params[index]? = some param) :
    (match (lowerContextAt module ctx impl).params[index]? with
      | some ty => if ty.isRefLike then
          (((lowerContextAt module ctx impl).roots.params.find? (·.1 == index)).map (·.2)).getD []
            |>.filterMap fun
              | .global global => some (Target.global global)
              | _ => none
        else []
      | none => []) = paramGlobals impl ctx index := by
  obtain ⟨identity, localVar, variableRow, scope, parameterType⟩ := implOk.params index param parameter
  have paramType : (lowerContextAt module ctx impl).params[index]? = some localVar.ty := by
    simp only [lowerContextAt, lowerImpl, List.getElem?_map]
    have row : impl.params.toList[index]? = some param := by simpa using parameter
    rw [row]
    simp [tyOfVar, identity, variableRow]
  have rootRow := lowerContextRootInfo_parameter_lookup (ctx := ctx) parameter
  rw [identity] at rootRow
  simp only [paramType, paramGlobals, variableRow]
  change (if localVar.ty.isRefLike then
    (((lowerContextRootInfo ctx impl).params.find? (·.1 == index)).map (·.2)).getD [] |>.filterMap
      (fun | .global global => some (Target.global global) | _ => none)
    else []) = _
  rw [rootRow]
  cases annotation : ctx.varRoots.find? (·.1 == index) <;> simp [annotation] <;> rfl

end Goose.Lower.Validation.SummaryPreservation
