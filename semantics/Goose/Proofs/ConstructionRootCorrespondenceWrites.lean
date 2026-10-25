import Goose.Proofs.ConstructionRootCorrespondenceCalls

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst VarId)

theorem bindRootsV_rooted (interpretation : RootInterpretation) (environment : PEnv)
    (chain : List Nat) (id : VarId) (roots : List RootRef) (value : Value)
    (checked : bindRootsV environment chain id roots = .ok ())
    (rooted : DirectValueRooted interpretation roots value) :
    ∃ annotation, environment.ann id = some annotation ∧
      DirectValueRooted interpretation annotation value := by
  cases declared : environment.impl.vars[id]? with
  | none => simp [bindRootsV, declared, Goose.Core.reject] at checked
  | some descriptor =>
    cases annotated : environment.ann id with
    | none => simp [bindRootsV, declared, annotated, Goose.Core.reject] at checked
    | some annotation =>
      refine ⟨annotation, rfl, ?_⟩
      apply directValueRooted_mono (lower := roots) (upper := annotation) _ rooted
      cases tested : subsetRoots roots annotation with
      | false => simp [bindRootsV, declared, annotated, tested, Goose.Core.reject, bind, Except.bind] at checked
      | true =>
        have members : ∀ root, root ∈ roots → root ∈ annotation := by
          simpa [subsetRoots] using tested
        exact fun {_} member => members _ member

private theorem lookup_rebound (entries : List (RootInst × Value))
    (root other : RootInst) (value : Value) (different : other ≠ root) :
    ((root, value) :: entries.filter (fun entry => entry.1 != root)).lookup other = entries.lookup other := by
  have mismatched : (other == root) = false := beq_eq_false_iff_ne.mpr different
  simp only [List.lookup, mismatched]
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨key, item⟩
    by_cases same : key = root
    · subst key
      simp only [List.filter, bne_self_eq_false, List.lookup, mismatched]
      exact ih
    · have retained : (key != root) = true := by simpa using same
      by_cases selected : other = key
      · subst key
        simp only [List.filter, retained, List.lookup, beq_self_eq_true]
      · have skipped : (other == key) = false := beq_eq_false_iff_ne.mpr selected
        simpa only [List.filter, retained, List.lookup, skipped] using ih

theorem bindStaticRoot_localCorrespondence (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (before : ExecutionState) (id : VarId) (root : RootInst)
    (value : Value) (annotation : List RootRef)
    (resolved : rootOf interpretation.environment id before = .ok root before)
    (annotated : (context.varRoots.find? (·.1 == id)).map Prod.snd = some annotation)
    (rooted : DirectValueRooted interpretation annotation value)
    (previous : LocalRootCorrespondence interpretation context visible before) :
    ∃ after, bindStaticRoot root value before = .ok () after ∧
      LocalRootCorrespondence interpretation context (id :: visible) after := by
  let after := { before with objects := (root, value) :: before.objects.filter (fun entry => entry.1 != root) }
  refine ⟨after, rfl, ?_⟩
  intro other member actual foundValue otherResolved found location reference
  have beforeResolved := rootOf_transfer interpretation other after before actual otherResolved
  by_cases equal : actual = root
  · subst actual
    have same := rootOf_variable_injective interpretation other id before root beforeResolved resolved
    subst other
    have sameValue : value = foundValue := by
      simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using found
    subst foundValue
    exact ⟨annotation, annotated, rooted location reference⟩
  · have oldMember : other ∈ visible := by
      rcases List.mem_cons.mp member with same | member
      · subst other
        rw [resolved] at beforeResolved
        cases beforeResolved
        exact (equal rfl).elim
      · exact member
    have oldFound : before.objects.lookup actual = some foundValue := by
      rw [← lookup_rebound before.objects root actual value equal]
      exact found
    exact previous other oldMember actual foundValue beforeResolved oldFound location reference

theorem bindRoot_objects (root : RootInst) (value : Value) (before : ExecutionState) :
    ∃ after, bindRoot root value before = .ok () after ∧
      after.objects = (root, value) :: before.objects.filter (fun entry => entry.1 != root) := by
  cases ordinal : before.objectOrdinals.lookup root <;> cases value <;>
    simp only [bindRoot, bind, EvalM.get, ordinal, Option.isNone, Bool.false_eq_true, ite_false,
      ite_true, setObjectOrdinal, EvalM.set, pure, reserveRootObject,
      liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set, bindStaticRoot] <;>
    exact ⟨_, rfl, rfl⟩

theorem bindRoot_localCorrespondence (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (before : ExecutionState) (id : VarId) (root : RootInst)
    (value : Value) (annotation : List RootRef)
    (resolved : rootOf interpretation.environment id before = .ok root before)
    (annotated : (context.varRoots.find? (·.1 == id)).map Prod.snd = some annotation)
    (rooted : DirectValueRooted interpretation annotation value)
    (previous : LocalRootCorrespondence interpretation context visible before) :
    ∃ after, bindRoot root value before = .ok () after ∧
      LocalRootCorrespondence interpretation context (id :: visible) after := by
  obtain ⟨simple, simpleBound, valid⟩ := bindStaticRoot_localCorrespondence interpretation context visible before
    id root value annotation resolved annotated rooted previous
  obtain ⟨after, bound, objects⟩ := bindRoot_objects root value before
  refine ⟨after, bound, localRootCorrespondence_objects interpretation context (id :: visible) simple after ?_ valid⟩
  simp only [bindStaticRoot, bind, EvalM.get, EvalM.set] at simpleBound
  cases simpleBound
  exact objects.symm

theorem writeLoc_localCorrespondence (fuel : Nat) (layout : LayoutEnv)
    (interpretation : RootInterpretation) (context : Context) (visible : List VarId)
    (before : ExecutionState) (id : VarId) (root : RootInst) (old value : Value) (annotation : List RootRef)
    (resolved : rootOf interpretation.environment id before = .ok root before)
    (found : before.objects.lookup root = some old)
    (annotated : (context.varRoots.find? (·.1 == id)).map Prod.snd = some annotation)
    (rooted : DirectValueRooted interpretation annotation value)
    (previous : LocalRootCorrespondence interpretation context visible before) :
    ∃ after, writeLoc (fuel + 1) layout ⟨root, []⟩ value before = .ok () after ∧
      LocalRootCorrespondence interpretation context (id :: visible) after := by
  obtain ⟨after, bound, valid⟩ := bindRoot_localCorrespondence interpretation context visible before
    id root value annotation resolved annotated rooted previous
  refine ⟨after, ?_, valid⟩
  simpa only [writeLoc, bind, EvalM.get, found, writeValuePath, pure] using bound

end Goose.Proofs.ConstructionRootCorrespondence
