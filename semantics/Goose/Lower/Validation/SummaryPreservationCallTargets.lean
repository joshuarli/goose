import Goose.Lower.Validation.SummaryPreservationCallEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem mapSummaryTargets_in_call {callee : Impl} {ctx : Context}
    {arguments : List (List RootRef)} (targets : List Target) :
    ∀ target ∈ mapSummaryTargets arguments targets,
      target ∈ mapCallTargets callee ctx arguments targets := by
  induction targets with
  | nil => simp [mapSummaryTargets]
  | cons head rest ih =>
    intro target member
    cases head with
    | global global =>
      simp only [mapSummaryTargets, List.mem_cons] at member
      exact member.elim (fun same => List.mem_cons.mpr (Or.inl same))
        (fun prior => List.mem_cons_of_mem _ (ih target prior))
    | param index =>
      simp only [mapSummaryTargets, List.mem_append] at member
      change target ∈ rootsTargets (arguments[index]?.getD []) ++
        paramGlobals callee ctx index ++ mapCallTargets callee ctx arguments rest
      exact member.elim (fun argument => List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inl argument)))) (fun prior => List.mem_append.mpr
          (Or.inr (ih target prior)))

theorem callGlobals_in_call {callee : Impl} {ctx : Context}
    {arguments : List (List RootRef)} (targets : List Target) :
    ∀ target ∈ targets.flatMap (fun
      | .param index => paramGlobals callee ctx index
      | .global _ => []), target ∈ mapCallTargets callee ctx arguments targets := by
  induction targets with
  | nil => simp
  | cons head rest ih =>
    intro target member
    cases head with
    | global global =>
      simp only [List.flatMap_cons, List.nil_append] at member
      exact List.mem_cons_of_mem _ (ih target member)
    | param index =>
      simp only [List.flatMap_cons, List.mem_append] at member
      change target ∈ rootsTargets (arguments[index]?.getD []) ++
        paramGlobals callee ctx index ++ mapCallTargets callee ctx arguments rest
      exact member.elim (fun global => List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inr global)))) (fun prior => List.mem_append.mpr
          (Or.inr (ih target prior)))

theorem storageTargets_filterGlobals (func : Func) (roots : List RootRef) :
    func.storageTargets (roots.filterMap fun
      | .global global => some (Target.global global)
      | _ => none) = (roots.filterMap fun
        | .global global => some (Target.global global)
        | _ => none) := by
  induction roots with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | param index => exact ih
    | «local» slot => exact ih
    | global global =>
      change Target.global global :: func.storageTargets _ = Target.global global :: _
      rw [ih]

theorem storageTargets_paramGlobals (func : Func) (callee : Impl) (ctx : Context) (index : Nat) :
    func.storageTargets (paramGlobals callee ctx index) = paramGlobals callee ctx index := by
  unfold paramGlobals
  cases callee.vars[index]? with
  | none => rfl
  | some localVar =>
    cases ctx.varRoots.find? (·.1 == index) with
    | none => rfl
    | some entry =>
      rcases entry with ⟨varId, roots⟩
      dsimp only
      split
      · exact storageTargets_filterGlobals func roots
      · rfl

theorem storageTargets_callGlobals (func : Func) (callee : Impl) (ctx : Context)
    (targets : List Target) :
    func.storageTargets (targets.flatMap (fun
      | .param index => paramGlobals callee ctx index
      | .global _ => [])) = targets.flatMap (fun
        | .param index => paramGlobals callee ctx index
        | .global _ => []) := by
  induction targets with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.flatMap_cons, storageTargets_append, ih]
    cases head with
    | global global => rfl
    | param index => rw [storageTargets_paramGlobals]


theorem lowerContextAt_callGlobals {module : Core.Module} {ctx : Context} {impl : Impl}
    (implOk : Core.Sound.ImplOk module impl) (targets : List Target)
    (bounds : ∀ index, Target.param index ∈ targets → index < impl.params.size) :
    targets.flatMap (fun
      | .param index =>
        match (lowerContextAt module ctx impl).params[index]? with
        | some ty => if ty.isRefLike then
            (((lowerContextAt module ctx impl).roots.params.find? (·.1 == index)).map (·.2)).getD []
              |>.filterMap fun
                | .global global => some (Target.global global)
                | _ => none
          else []
        | none => []
      | .global _ => []) = targets.flatMap (fun
        | .param index => paramGlobals impl ctx index
        | .global _ => []) := by
  apply congrArg List.flatten
  apply List.map_congr_left
  intro target member
  cases target with
  | global global => rfl
  | param index =>
    let param := impl.params[index]'(bounds index member)
    exact lowerContextAt_parameterGlobals implOk
      (show impl.params[index]? = some param from Array.getElem?_eq_getElem _)

theorem mapCallTargets_storage_below {func : Func} {callee : Impl} {ctx : Context}
    {actual source : List (List RootRef)}
    (arguments : ∀ (index : Nat) (target : Target),
      target ∈ func.storageTargets (rootsTargets (actual[index]?.getD [])) →
        target ∈ rootsTargets (source[index]?.getD [])) (targets : List Target) :
    ∀ target ∈ func.storageTargets (addTargets (mapSummaryTargets actual targets)
      (targets.flatMap fun | .param index => paramGlobals callee ctx index | .global _ => [])),
      target ∈ mapCallTargets callee ctx source targets := by
  intro target member
  rcases storageTargets_addTargets_origin member with actualMember | globals
  · exact mapSummaryTargets_in_call targets target
      (mapSummaryTargets_storage_below arguments targets target actualMember)
  · rw [storageTargets_callGlobals] at globals
    exact callGlobals_in_call targets target globals

end Goose.Lower.Validation.SummaryPreservation
