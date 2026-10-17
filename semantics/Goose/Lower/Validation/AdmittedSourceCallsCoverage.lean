import Goose.Lower.Validation.AdmittedSourceCallsTransport
import Goose.GIR.RootBoundsRefinement

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

private theorem union_mem {left right : List RootRef} {root : RootRef} :
    root ∈ unionRoots left right ↔ root ∈ left ∨ root ∈ right :=
  ⟨Sound.unionRoots_mem left right root,
    fun member => member.elim (Sound.unionRoots_left left right root)
      (Sound.unionRoots_right left right root)⟩

private theorem flattened_mem (roots accumulated : List RootRef) (root : RootRef) :
    root ∈ roots.foldl (fun prior next => unionRoots prior [next]) accumulated ↔
      root ∈ accumulated ∨ root ∈ roots := by
  induction roots generalizing accumulated with
  | nil => simp
  | cons first rest inductionHypothesis =>
    simp only [List.foldl_cons, inductionHypothesis, union_mem, List.mem_singleton,
      List.mem_cons, or_assoc, List.not_mem_nil, false_or]

theorem argumentContents_mem {func : Func} {provenance : Prov} {value : ValueId}
    {root : RootRef} :
    root ∈ argumentContents func provenance value ↔
      ∃ receiver ∈ rootsAt provenance.vals value,
        ∃ content ∈ func.receiverContentCeiling provenance receiver,
          root ∈ func.expandParameterRoot content := by
  simp only [argumentContents, flattened_mem, List.not_mem_nil, false_or, List.mem_flatMap]
  apply exists_congr
  intro receiver
  apply and_congr_right
  intro member
  cases receiver with
  | «local» slot => rfl
  | global global => rfl
  | param parameter =>
    cases found : func.params[parameter]? with
    | none => simp [Func.receiverContentCeiling, found]
    | some type => simp [Func.receiverContentCeiling, found]

theorem mapContentRoots_mem {func : Func} {provenance : Prov} {arguments : List ValueId}
    {declared : List RootRef} {root : RootRef} :
    root ∈ mapContentRoots func provenance arguments declared ↔
      root ∈ (mapRawContentRoots provenance arguments declared).flatMap func.expandParameterRoot := by
  simp only [mapContentRoots, flattened_mem, List.not_mem_nil, false_or, List.mem_flatMap,
    mapRawContentRoots, List.mem_eraseDups]
  constructor
  · rintro ⟨declaredRoot, declaredMember, member⟩
    cases declaredRoot with
    | «local» slot => simp at member
    | global global =>
      have same : root = RootRef.global global := List.mem_singleton.mp member
      subst root
      exact ⟨.global global, ⟨.global global, declaredMember, by simp⟩,
        by simp [Func.expandParameterRoot]⟩
    | param parameter =>
      cases found : arguments[parameter]? with
      | none => simp [found] at member
      | some value =>
        simp only [found, List.mem_flatMap] at member
        obtain ⟨actual, actualMember, expandedMember⟩ := member
        exact ⟨actual, ⟨.param parameter, declaredMember, by simpa [found] using actualMember⟩,
          expandedMember⟩
  · rintro ⟨actual, ⟨declaredRoot, declaredMember, member⟩, expandedMember⟩
    refine ⟨declaredRoot, declaredMember, ?_⟩
    cases declaredRoot with
    | «local» slot => simp at member
    | global global =>
      have same : actual = RootRef.global global := List.mem_singleton.mp member
      subst actual
      simpa only [Func.expandParameterRoot, List.mem_singleton] using expandedMember
    | param parameter =>
      cases found : arguments[parameter]? with
      | none => simp [found] at member
      | some value =>
        simp only [found]
        apply List.mem_flatMap.mpr
        exact ⟨actual, by simpa [found] using member, expandedMember⟩

theorem call_content_coverage_of_receivers
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {declared : List RootRef} {value : ValueId}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (nonempty : ∃ root, root ∈ rootsAt provenance.vals value)
    (receivers : func.admittedCallReceiver provenance value
      (mapRawContentRoots provenance arguments declared) = true) :
    argumentContents func provenance value ⊆ mapContentRoots func provenance arguments declared ∧
      mapContentRoots func provenance arguments declared ⊆ argumentContents func provenance value := by
  have bounds := List.all_eq_true.mp receivers
  constructor
  · intro root member
    obtain ⟨receiver, receiverMember, content, contentMember, expandedMember⟩ :=
      argumentContents_mem.mp member
    have reverse : func.rootsWithin (func.receiverContentCeiling provenance receiver)
        (mapRawContentRoots provenance arguments declared) = true := by
      have checked := bounds receiver receiverMember
      simp only [Bool.and_eq_true] at checked
      exact checked.2
    apply mapContentRoots_mem.mpr
    exact ((Func.rootsWithin_eq_true _ _ _).mp reverse).expanded closed
      content contentMember root expandedMember
  · intro root member
    obtain ⟨receiver, receiverMember⟩ := nonempty
    obtain ⟨content, contentMember, expandedMember⟩ := List.mem_flatMap.mp
      (mapContentRoots_mem.mp member)
    have forward : func.rootsWithin (mapRawContentRoots provenance arguments declared)
        (func.receiverContentCeiling provenance receiver) = true := by
      have checked := bounds receiver receiverMember
      simp only [Bool.and_eq_true] at checked
      exact checked.1
    obtain ⟨origin, originMember, concreteMember⟩ := List.mem_flatMap.mp
      (((Func.rootsWithin_eq_true _ _ _).mp forward).expanded closed
        content contentMember root expandedMember)
    exact argumentContents_mem.mpr ⟨receiver, receiverMember, origin, originMember, concreteMember⟩

end Goose.Lower.Validation.AdmittedSourceCalls
