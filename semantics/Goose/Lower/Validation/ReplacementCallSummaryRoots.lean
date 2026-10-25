import Goose.Lower.Validation.ReplacementCallReferenceApart
import Goose.Lower.Validation.SummaryPreservationCallTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem forIn_ownerAppend {α : Type} (items : List α)
    (step : α → List DemandOwner → V (ForInStep (List DemandOwner)))
    (added : α → List DemandOwner)
    (appendStep : ∀ item, item ∈ items → ∀ previous following,
      step item previous = .ok following → following = .yield (previous ++ added item))
    {previous following : List DemandOwner}
    (checked : forIn items previous step = .ok following) :
    following = previous ++ items.flatMap added := by
  induction items generalizing previous with
  | nil => simpa only [List.forIn_nil, ex_pure_ok, List.flatMap_nil, List.append_nil] using checked
  | cons item rest ih =>
    simp only [List.forIn_cons] at checked
    obtain ⟨control, head, tail⟩ := (ex_bind_ok _ _ _).mp checked
    have controlEq := appendStep item (by simp) previous control head
    have result := ih (fun item member => appendStep item (List.mem_cons_of_mem _ member))
      (by simpa only [controlEq] using tail)
    simpa only [List.flatMap_cons, List.append_assoc] using result

private def targetOwnerEntries (access : AccessEnv) (callee : Impl)
    (ctx : Context) (actual : List (List RootRef)) : Target → List DemandOwner
  | .global global => [⟨access.rootType? (.global global), [.global global]⟩]
  | .param index =>
    ((actual[index]?.getD []) ++ (paramGlobals callee ctx index).filterMap (fun
      | .global global => some (RootRef.global global)
      | _ => none)).map (fun reference => ⟨access.rootType? reference, [reference]⟩)

theorem targetOwners_roots {access : AccessEnv} {callee : Impl} {ctx : Context}
    {actual : List (List RootRef)} {targets : List Target} {owners : List DemandOwner}
    (checked : access.targetOwners callee ctx actual targets = .ok owners) :
    owners.flatMap DemandOwner.roots = targets.flatMap (fun
      | .global global => [.global global]
      | .param index => actual[index]?.getD [] ++ (paramGlobals callee ctx index).filterMap (fun
        | .global global => some (.global global)
        | _ => none)) := by
  unfold AccessEnv.targetOwners at checked
  obtain ⟨result, loop, resultEq⟩ := (ex_bind_ok _ _ _).mp checked
  have equal : owners = result := (ex_pure_ok _ _).mp resultEq
  subst owners
  have appended : result = [] ++ targets.flatMap (targetOwnerEntries access callee ctx actual) := by
    apply forIn_ownerAppend targets _ (targetOwnerEntries access callee ctx actual) ?_ loop
    intro target member previous following stepChecked
    cases target with
    | global global =>
      dsimp only at stepChecked
      cases globalAt : access.mod.globals[global]? with
      | none => simp [globalAt, reject, Functor.map, Except.map] at stepChecked
      | some declaration =>
        have same := (ex_pure_ok _ _).mp (by simpa only [globalAt] using stepChecked)
        simpa only [targetOwnerEntries, AccessEnv.rootType?, globalAt, Option.map_some] using same
    | param index =>
      dsimp only at stepChecked
      cases actualAt : actual[index]? with
      | none => simp [actualAt, reject, Functor.map, Except.map] at stepChecked
      | some roots =>
        simp only [actualAt] at stepChecked
        obtain ⟨next, rootLoop, output⟩ := (ex_bind_ok _ _ _).mp stepChecked
        have same := (ex_pure_ok _ _).mp output
        subst following
        have appended := forIn_ownerAppend _ _
          (fun root => [⟨access.rootType? root, [root]⟩])
          (fun root _ previous following checked => (ex_pure_ok _ _).mp checked) rootLoop
        apply congrArg ForInStep.yield
        simp only [targetOwnerEntries, actualAt, Option.getD_some]
        rw [← List.map_eq_flatMap] at appended
        apply appended.trans
        congr 3

  rw [appended, List.nil_append, List.flatMap_assoc]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro target member
  cases target <;> simp [targetOwnerEntries, List.flatMap_map]

theorem lowerContext_parameterGlobalRoots_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {index : Nat} {parameter : Param} (parameterAt : impl.params[index]? = some parameter) :
    (((((lowerContextAt module context impl).roots.params.find? (·.1 == index)).map (·.2)).getD [])
        |>.filterMap (fun | .global global => some (RootRef.global global) | _ => none)) =
      (paramGlobals impl context index).filterMap
        (fun | .global global => some (RootRef.global global) | _ => none) := by
  obtain ⟨checkedImpl, checkedAt, checked⟩ :=
    (validate_modOk module accepted).ctx contextIndex context contextAt
  rw [implAt] at checkedAt
  cases checkedAt
  have implOk := (validate_modOk module accepted).impl context.impl impl implAt
  obtain ⟨identity, localVar, variableAt, scope, parameterType⟩ := implOk.params index parameter parameterAt
  have row := lowerContextRootInfo_parameter_lookup (ctx := context) parameterAt
  rw [identity] at row
  change (((((lowerContextRootInfo context impl).params.find? (·.1 == index)).map (·.2)).getD [])
        |>.filterMap (fun | .global global => some (RootRef.global global) | _ => none)) = _
  rw [row]
  cases annotationAt : context.varRoots.find? (·.1 == index) with
  | none => simp [annotationAt, paramGlobals, variableAt]
  | some annotation =>
    have key : annotation.1 = index := eq_of_beq (List.find?_some (p := fun entry : VarId × List RootRef => entry.1 == index)
      (a := annotation) annotationAt)
    obtain ⟨actual, actualAt, refLike, _⟩ := Core.Declarative.annotationRows_sound
      module impl context checked.annotationShape annotation.1 annotation.2
      (List.mem_of_find?_eq_some annotationAt)
    rw [key, variableAt] at actualAt
    cases actualAt
    simp only [annotationAt, Option.map_some, Option.getD_some, paramGlobals, variableAt, refLike, ↓reduceIte]
    rw [List.filterMap_filterMap]
    apply congrArg (fun mapper => annotation.2.filterMap mapper)
    funext reference
    cases reference <;> rfl

theorem callSummaryRoots_known_within {module : GIR.Module} {callee : Func}
    {queries : ReplacementQueries} {function : FnId} {arguments : List ValueId}
    {summary : Core.Summary} {source : List RootRef}
    (calleeAt : module.funcs[function]? = some callee)
    (summaryAt : callee.summary = .known summary)
    (globals : ∀ global, Target.global global ∈ summary.reads ++ summary.writes ++
      summary.grows ++ summary.shrinks ++ summary.rebinds → RootRef.global global ∈ source)
    (parameters : ∀ index, Target.param index ∈ summary.reads ++ summary.writes ++
      summary.grows ++ summary.shrinks ++ summary.rebinds →
      ∃ argument, arguments[index]? = some argument ∧
        ReplacementRootsWithin (queries.ownerDependencies argument) source ∧
        (∀ global, RootRef.global global ∈
          (((callee.roots.params.find? (·.1 == index)).map (·.2)).getD []) →
          RootRef.global global ∈ source)) :
    ReplacementRootsWithin (callSummaryRoots module queries function arguments) source := by
  let targets := summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds
  let step : List RootRef → Target → Option (List RootRef) := fun roots target => do
    match target with
    | .global global => pure (unionRoots roots [.global global])
    | .param index =>
      let argument ← arguments[index]?
      let actual ← queries.ownerDependencies argument
      let annotated := (((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [])
        |>.filterMap fun | .global global => some (RootRef.global global) | _ => none
      pure (unionRoots roots (actual ++ annotated))
  have merge : ∀ {left right : List RootRef}, left ⊆ source → right ⊆ source →
      unionRoots left right ⊆ source := by
    intro left right leftBound rightBound root member
    exact (Core.Sound.unionRoots_mem _ _ _ member).elim (fun h => leftBound h) (fun h => rightBound h)
  have accumulate : ∀ rest : List Target, rest ⊆ targets → ∀ prior, prior ⊆ source →
      ReplacementRootsWithin (rest.foldlM step prior) source := by
    intro rest
    induction rest with
    | nil => intro _ prior bounded; exact ⟨prior, rfl, bounded⟩
    | cons target rest ih =>
      intro included prior bounded
      have targetAt := included (by simp : target ∈ target :: rest)
      have restBound : rest ⊆ targets := fun {_} member => included (List.mem_cons_of_mem _ member)
      cases target with
      | global global =>
        have globalBound : [RootRef.global global] ⊆ source := by
          intro root member
          exact List.mem_singleton.mp member ▸ globals global targetAt
        simpa [List.foldlM_cons, step] using ih restBound _ (merge bounded globalBound)
      | param index =>
        obtain ⟨argument, argumentAt, known, annotationBound⟩ := parameters index targetAt
        obtain ⟨actual, actualAt, actualBound⟩ := known
        have annotated : (actual ++ ((((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [])
            |>.filterMap fun | .global global => some (RootRef.global global) | _ => none)) ⊆ source := by
          intro root member
          rcases List.mem_append.mp member with actualMember | annotationMember
          · exact actualBound actualMember
          · obtain ⟨target, targetMember, targetEq⟩ := List.mem_filterMap.mp annotationMember
            cases target with
            | param i => simp at targetEq
            | «local» slot => simp at targetEq
            | global global =>
              have same : RootRef.global global = root := Option.some.inj targetEq
              exact same ▸ annotationBound global targetMember
        simpa [List.foldlM_cons, step, argumentAt, actualAt] using
          ih restBound _ (merge bounded annotated)
  have result := accumulate targets (fun {_} member => member) [] (by simp)
  suffices equal : callSummaryRoots module queries function arguments = targets.foldlM step [] by
    rw [equal]
    exact result
  unfold callSummaryRoots
  simp only [calleeAt, summaryAt]
  apply congrArg (fun operation => targets.foldlM operation [])
  funext prior target
  cases target with
  | global global => rfl
  | param index =>
    dsimp only [step]
    congr 4

#print axioms lowerContext_parameterGlobalRoots_of_accepted
#print axioms targetOwners_roots
#print axioms callSummaryRoots_known_within

end Goose.Lower.Validation
