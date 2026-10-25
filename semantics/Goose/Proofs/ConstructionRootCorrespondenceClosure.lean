import Goose.Proofs.ConstructionRootCorrespondenceCalls

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (VarId)

def AnnotationExtends (before after : Context) : Prop :=
  ∀ id roots, (before.varRoots.find? (·.1 == id)).map Prod.snd = some roots →
    ∃ upper, (after.varRoots.find? (·.1 == id)).map Prod.snd = some upper ∧ roots ⊆ upper

theorem annotationExtends_refl (context : Context) : AnnotationExtends context context := by
  intro id roots found
  exact ⟨roots, found, fun {_} member => member⟩

theorem annotationExtends_trans {first second third : Context}
    (left : AnnotationExtends first second) (right : AnnotationExtends second third) :
    AnnotationExtends first third := by
  intro id roots found
  obtain ⟨middle, middleAt, included⟩ := left id roots found
  obtain ⟨upper, upperAt, covered⟩ := right id middle middleAt
  exact ⟨upper, upperAt, fun {_} member => covered (included member)⟩

theorem annotationExtends_map (context : Context) (variableId : VarId) (added : List RootRef) :
    AnnotationExtends context { context with varRoots := context.varRoots.map fun (id, previous) =>
      (id, if id == variableId then unionRoots previous added else previous) } := by
  intro id roots found
  simp only [List.find?_map, Function.comp_def, Option.map_map] 
  cases selected : context.varRoots.find? (·.1 == id) with
  | none => simp [selected] at found
  | some entry =>
    have equal : entry.1 = id := by simpa using List.find?_some selected
    simp only [selected, Option.map_some, Option.some.injEq] at found
    subst roots
    refine ⟨if entry.1 == variableId then unionRoots entry.2 added else entry.2, ?_, ?_⟩
    · simp only [Option.map_some]
    · split
      · intro root member
        exact (mem_unionRoots root entry.2 added).mpr (.inl member)
      · exact fun {_} member => member

private theorem success_bind {α β : Type} (action : Goose.Core.V α)
    (next : α → Goose.Core.V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem forIn_preserves {α β : Type} (rows : List α) (initial : β)
    (body : α → β → Goose.Core.V (ForInStep β)) (invariant : β → Prop)
    (valid : invariant initial)
    (preserved : ∀ row before step, invariant before → body row before = .ok step →
      invariant step.value) (final : β) (checked : forIn rows initial body = .ok final) :
    invariant final := by
  induction rows generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at checked
    subst final
    exact valid
  | cons row rows ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, evaluated, remaining⟩ := (success_bind _ _ _).mp checked
    have after := preserved row initial step valid evaluated
    cases step with
    | done value =>
      simp only [pure, Except.pure, Except.ok.injEq] at remaining
      subst final
      exact after
    | yield value => exact ih value after remaining

theorem parameterBodyRootContext_annotationExtends (module : Module) (implementation : Impl)
    (context result : Context) (checked : parameterBodyRootContext module implementation context = .ok result) :
    AnnotationExtends context result := by
  unfold parameterBodyRootContext at checked
  split at checked
  · simp only [pure, Except.pure, Except.ok.injEq] at checked
    subst result
    exact annotationExtends_refl context
  · dsimp only [] at checked
    simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at checked
    obtain ⟨final, loop, returned⟩ := (success_bind _ _ _).mp checked
    let invariant (current : Option Context × Context) :=
      AnnotationExtends context current.2 ∧
        ∀ output, current.1 = some output → AnnotationExtends context output
    have initial : invariant (none, context) :=
      ⟨annotationExtends_refl context, fun _ absent => by cases absent⟩
    have maintained := forIn_preserves _ _ _ invariant initial (by
      intro index current step valid evaluated
      obtain ⟨next, updates, finished⟩ := (success_bind _ _ _).mp evaluated
      have extended := forIn_preserves _ current.2 _ (AnnotationExtends current.2)
        (annotationExtends_refl current.2) (by
          intro assignment before step valid updated
          obtain ⟨variableId, expression⟩ := assignment
          obtain ⟨roots, computed, completed⟩ := (success_bind _ _ _).mp updated
          simp only [pure, Except.pure, Except.ok.injEq] at completed
          subst step
          exact annotationExtends_trans valid (annotationExtends_map before variableId roots)) next updates
      split at finished
      · simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst step
        exact ⟨valid.1, fun _ equal => by cases equal; exact valid.1⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst step
        exact ⟨annotationExtends_trans valid.1 extended, fun _ absent => by cases absent⟩) final loop
    cases output : final.1 with
    | none => simp [output, Goose.Core.reject] at returned
    | some value =>
      simp only [output, pure, Except.pure, Except.ok.injEq] at returned
      subst result
      exact maintained.2 value output

theorem localRootCorrespondence_annotationExtends (interpretation : RootInterpretation)
    (before after : Context) (visible : List VarId) (state : ExecutionState)
    (extended : AnnotationExtends before after)
    (valid : LocalRootCorrespondence interpretation before visible state) :
    LocalRootCorrespondence interpretation after visible state := by
  intro id member root value resolved found location reference
  obtain ⟨roots, annotation, rooted⟩ := valid id member root value resolved found location reference
  obtain ⟨upper, upperAt, included⟩ := extended id roots annotation
  exact ⟨upper, upperAt, rootIn_mono included rooted⟩

private def addParameterRoots (context : Context) (variableId : VarId) (roots : List RootRef) : Context :=
  { context with varRoots := context.varRoots.map fun (id, previous) =>
    (id, if id == variableId then unionRoots previous roots else previous) }

private def parameterRootStep (module : Module) (implementation : Impl) (source : Context)
    (assignment : VarId × Expr) (current : Context) : Goose.Core.V (ForInStep Context) := do
  let roots ← (AccessEnv.mk module implementation source).exprRoots assignment.2
  pure (.yield (addParameterRoots current assignment.1 roots))

private def parameterRootPass (module : Module) (implementation : Impl) (assignments : List (VarId × Expr))
    (context : Context) : Goose.Core.V Context :=
  forIn assignments context (parameterRootStep module implementation context)

private theorem addParameterRoots_find (context : Context) (variableId id : VarId)
    (added roots : List RootRef)
    (found : (context.varRoots.find? (·.1 == id)).map Prod.snd = some roots) :
    ((addParameterRoots context variableId added).varRoots.find? (·.1 == id)).map Prod.snd =
      some (if id == variableId then unionRoots roots added else roots) := by
  simp only [addParameterRoots, List.find?_map, Function.comp_def, Option.map_map]
  cases selected : context.varRoots.find? (·.1 == id) with
  | none => simp [selected] at found
  | some entry =>
    have equal : entry.1 = id := by simpa using List.find?_some selected
    simp only [selected, Option.map_some, Option.some.injEq] at found
    subst roots
    simp only [Option.map_some, equal]

private theorem parameterRootUpdates_extend (module : Module) (implementation : Impl) (source : Context)
    (assignments : List (VarId × Expr)) (initial final : Context)
    (checked : forIn assignments initial (parameterRootStep module implementation source) = .ok final) :
    AnnotationExtends initial final := by
  apply forIn_preserves assignments initial _ (AnnotationExtends initial) (annotationExtends_refl initial)
    (fun assignment current step valid evaluated => ?_) final checked
  obtain ⟨variableId, expression⟩ := assignment
  unfold parameterRootStep at evaluated
  obtain ⟨roots, computed, completed⟩ := (success_bind _ _ _).mp evaluated
  simp only [pure, Except.pure, Except.ok.injEq] at completed
  subst step
  exact annotationExtends_trans valid (annotationExtends_map current variableId roots)

private theorem parameterRootUpdates_cover (module : Module) (implementation : Impl) (source : Context)
    (assignments : List (VarId × Expr)) (initial final : Context)
    (checked : forIn assignments initial (parameterRootStep module implementation source) = .ok final)
    (variableId : VarId) (expression : Expr) (member : (variableId, expression) ∈ assignments)
    (roots annotation : List RootRef)
    (computed : (AccessEnv.mk module implementation source).exprRoots expression = .ok roots)
    (annotated : (initial.varRoots.find? (·.1 == variableId)).map Prod.snd = some annotation) :
    ∃ upper, (final.varRoots.find? (·.1 == variableId)).map Prod.snd = some upper ∧ roots ⊆ upper := by
  induction assignments generalizing initial annotation with
  | nil => cases member
  | cons assignment assignments ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := (success_bind _ _ _).mp checked
    unfold parameterRootStep at first
    obtain ⟨added, evaluated, completed⟩ := (success_bind _ _ _).mp first
    simp only [pure, Except.pure, Except.ok.injEq] at completed
    subst step
    rcases List.mem_cons.mp member with equal | member
    · subst assignment
      rw [computed] at evaluated
      cases evaluated
      have expanded := addParameterRoots_find initial variableId variableId roots annotation annotated
      simp only [beq_self_eq_true, ite_true] at expanded
      obtain ⟨upper, upperAt, included⟩ :=
        parameterRootUpdates_extend module implementation source assignments _ final remaining
          variableId (unionRoots annotation roots) expanded
      refine ⟨upper, upperAt, ?_⟩
      intro root member
      exact included ((mem_unionRoots root annotation roots).mpr (.inr member))
    · obtain ⟨middle, middleAt, _⟩ := annotationExtends_map initial assignment.1 added variableId annotation annotated
      exact ih _ remaining member middle middleAt

theorem parameterBodyRootContext_coversRebinding (module : Module) (implementation : Impl)
    (context result : Context) (checked : parameterBodyRootContext module implementation context = .ok result)
    (variableId : VarId) (expression : Expr)
    (member : (variableId, expression) ∈ mutableParameterRebindings implementation)
    (roots annotation : List RootRef)
    (computed : (AccessEnv.mk module implementation result).exprRoots expression = .ok roots)
    (annotated : (result.varRoots.find? (·.1 == variableId)).map Prod.snd = some annotation) :
    roots ⊆ annotation := by
  unfold parameterBodyRootContext at checked
  split at checked
  · rename_i disabled
    unfold mutableParameterRebindings at member
    obtain ⟨_, mutable⟩ := List.mem_filter.mp member
    change ((implementation.vars[variableId]?).any
        (fun localVar => localVar.kind == .mutable && localVar.ty.isRefLike) &&
      implementation.params.any (fun parameter => parameter.var == variableId && parameter.mode == .byValue)) = true
        at mutable
    have parameterExists := (Bool.and_eq_true _ _).mp mutable |>.2
    obtain ⟨index, inBounds, selected⟩ := Array.any_eq_true.mp parameterExists
    have equal : implementation.params[index].var = variableId := by
      simpa using ((Bool.and_eq_true _ _).mp selected).1
    have enabled : implementation.params.any (fun parameter =>
        (implementation.vars[parameter.var]?).any
            (fun localVar => localVar.kind == .mutable && localVar.ty.isRefLike) &&
          implementation.params.any (fun current => current.var == parameter.var && current.mode == .byValue)) = true := by
      apply Array.any_eq_true.mpr
      exact ⟨index, inBounds, by simpa only [equal] using mutable⟩
    change (!(implementation.params.any (fun parameter =>
        (implementation.vars[parameter.var]?).any
            (fun localVar => localVar.kind == .mutable && localVar.ty.isRefLike) &&
          implementation.params.any (fun current => current.var == parameter.var && current.mode == .byValue)))) = true
        at disabled
    simp only [enabled, Bool.not_true] at disabled
    cases disabled
  · dsimp only [] at checked
    simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at checked
    obtain ⟨final, loop, returned⟩ := (success_bind _ _ _).mp checked
    let stable (context : Context) := ∃ next,
      parameterRootPass module implementation (mutableParameterRebindings implementation) context = .ok next ∧
        next.varRoots = context.varRoots
    let invariant (current : Option Context × Context) := ∀ output, current.1 = some output → stable output
    have initial : invariant (none, context) := fun _ absent => by cases absent
    have maintained := forIn_preserves _ _ _ invariant initial (by
      intro index current step valid evaluated
      obtain ⟨next, evaluatedPass, finished⟩ := (success_bind _ _ _).mp evaluated
      have pass : parameterRootPass module implementation (mutableParameterRebindings implementation) current.2 =
          .ok next := by
        unfold parameterRootPass
        change forIn (mutableParameterRebindings implementation) current.2
          (fun assignment before => parameterRootStep module implementation current.2 assignment before) = .ok next
        simpa only [parameterRootStep, addParameterRoots] using evaluatedPass
      split at finished
      · rename_i equal
        simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst step
        intro output same
        cases same
        exact ⟨next, pass, by simpa using equal⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst step
        intro output absent
        cases absent) final loop
    have stableResult : stable result := by
      cases output : final.1 with
      | none => simp [output, Goose.Core.reject] at returned
      | some value =>
        simp only [output, pure, Except.pure, Except.ok.injEq] at returned
        subst result
        exact maintained value output
    obtain ⟨next, evaluated, equal⟩ := stableResult
    obtain ⟨upper, upperAt, included⟩ := parameterRootUpdates_cover module implementation result
      (mutableParameterRebindings implementation) result next evaluated variableId expression member roots annotation
      computed annotated
    rw [equal, annotated] at upperAt
    cases upperAt
    exact included

end Goose.Proofs.ConstructionRootCorrespondence
