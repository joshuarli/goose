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

end Goose.Proofs.ConstructionRootCorrespondence
