import Goose.Proofs.ConstructionRootCorrespondence

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst)

def CallInterpretation (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) : RootInterpretation :=
  ⟨callee, caller.globalCount, fun index root =>
    ∃ roots, arguments[index]? = some roots ∧ RootIn caller roots root⟩

theorem mapCalleeRoots_rooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (symbolic : RootRef) (mapped : List RootRef)
    (checked : mapCalleeRoots arguments symbolic = .ok mapped) (root : RootInst)
    (instantiated : Instantiates (CallInterpretation caller callee arguments) symbolic root) :
    RootIn caller mapped root := by
  cases instantiated with
  | global id declared =>
    simp only [mapCalleeRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    exact ⟨.global id, by simp, .global id declared⟩
  | static id synthetic =>
    simp only [mapCalleeRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    exact ⟨.static, by simp, .static id synthetic⟩
  | «local» id descriptor scope declared active =>
    simp [mapCalleeRoots, Goose.Core.reject] at checked
  | parameter id actual supplied =>
    obtain ⟨roots, present, rooted⟩ := supplied
    simp only [mapCalleeRoots, present, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    exact rooted

theorem mapCalleeRoots_reflects (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (symbolic : RootRef) (mapped : List RootRef)
    (checked : mapCalleeRoots arguments symbolic = .ok mapped) (root : RootInst)
    (rooted : RootIn caller mapped root) : Instantiates (CallInterpretation caller callee arguments) symbolic root := by
  cases symbolic with
  | param index =>
    cases supplied : arguments[index]? with
    | none => simp [mapCalleeRoots, supplied, Goose.Core.reject] at checked
    | some roots =>
      simp only [mapCalleeRoots, supplied, pure, Except.pure, Except.ok.injEq] at checked
      subst mapped
      exact .parameter index root ⟨roots, supplied, rooted⟩
  | «local» id => simp [mapCalleeRoots, Goose.Core.reject] at checked
  | global id =>
    simp only [mapCalleeRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    obtain ⟨symbolic, member, actual⟩ := rooted
    have equal := List.mem_singleton.mp member
    subst symbolic
    cases actual with
    | global id declared => exact .global id declared
  | static =>
    simp only [mapCalleeRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    obtain ⟨symbolic, member, actual⟩ := rooted
    have equal := List.mem_singleton.mp member
    subst symbolic
    cases actual with
    | static id synthetic => exact .static id synthetic

theorem mem_unionRoots (root : RootRef) (left right : List RootRef) :
    root ∈ unionRoots left right ↔ root ∈ left ∨ root ∈ right := by
  unfold unionRoots
  induction right generalizing left with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> by_cases same : root = head <;> simp_all

theorem rootIn_unionRoots (interpretation : RootInterpretation) (left right : List RootRef)
    (root : RootInst) : RootIn interpretation (unionRoots left right) root ↔
      RootIn interpretation left root ∨ RootIn interpretation right root := by
  simp only [RootIn, mem_unionRoots]
  constructor
  · rintro ⟨symbolic, member | member, instantiated⟩
    · exact Or.inl ⟨symbolic, member, instantiated⟩
    · exact Or.inr ⟨symbolic, member, instantiated⟩
  · rintro (⟨symbolic, member, instantiated⟩ | ⟨symbolic, member, instantiated⟩)
    · exact ⟨symbolic, Or.inl member, instantiated⟩
    · exact ⟨symbolic, Or.inr member, instantiated⟩

theorem mapResultRoots_rooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (declared accumulator mapped : List RootRef)
    (checked : mapResultRoots arguments accumulator declared = .ok mapped) (root : RootInst)
    (rooted : RootIn caller accumulator root ∨
      RootIn (CallInterpretation caller callee arguments) declared root) :
    RootIn caller mapped root := by
  induction declared generalizing accumulator with
  | nil =>
    simp only [mapResultRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    rcases rooted with rooted | ⟨symbolic, member, _⟩
    · exact rooted
    · cases member
  | cons head rest ih =>
    simp only [mapResultRoots] at checked
    cases mapping : mapCalleeRoots arguments head with
    | error reason => simp [mapping, bind, Except.bind] at checked
    | ok roots =>
      simp only [mapping, bind, Except.bind] at checked
      apply ih (unionRoots accumulator roots) checked
      rcases rooted with rooted | ⟨symbolic, member, instantiated⟩
      · exact Or.inl ((rootIn_unionRoots caller accumulator roots root).mpr (.inl rooted))
      · rcases List.mem_cons.mp member with equal | member
        · subst symbolic
          exact Or.inl ((rootIn_unionRoots caller accumulator roots root).mpr
            (.inr (mapCalleeRoots_rooted caller callee arguments head roots mapping root instantiated)))
        · exact Or.inr ⟨symbolic, member, instantiated⟩

theorem mapResultRoots_reflects (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (declared accumulator mapped : List RootRef)
    (checked : mapResultRoots arguments accumulator declared = .ok mapped) (root : RootInst)
    (rooted : RootIn caller mapped root) :
    RootIn caller accumulator root ∨ RootIn (CallInterpretation caller callee arguments) declared root := by
  induction declared generalizing accumulator with
  | nil =>
    simp only [mapResultRoots, pure, Except.pure, Except.ok.injEq] at checked
    subst mapped
    exact Or.inl rooted
  | cons head rest ih =>
    simp only [mapResultRoots] at checked
    cases mapping : mapCalleeRoots arguments head with
    | error reason => simp [mapping, bind, Except.bind] at checked
    | ok roots =>
      simp only [mapping, bind, Except.bind] at checked
      rcases ih (unionRoots accumulator roots) checked with inherited | ⟨symbolic, member, actual⟩
      · rcases (rootIn_unionRoots caller accumulator roots root).mp inherited with old | added
        · exact Or.inl old
        · exact Or.inr ⟨head, by simp,
            mapCalleeRoots_reflects caller callee arguments head roots mapping root added⟩
      · exact Or.inr ⟨symbolic, List.mem_cons_of_mem head member, actual⟩

theorem checkArgRoots_annotation (callee : Impl) (context : Context)
    (arguments : List (List RootRef)) (index : Nat) (parameter : Param) (descriptor : LocalVar)
    (roots : List RootRef) (parameterAt : callee.params[index]? = some parameter)
    (variableAt : callee.vars[parameter.var]? = some descriptor)
    (refLike : descriptor.ty.isRefLike = true)
    (annotation : context.varRoots.find? (·.1 == parameter.var) = some (parameter.var, roots))
    (checked : checkArgRoots callee context arguments index = .ok ()) :
    roots = [.param index] ∨ arguments[index]?.getD [] ⊆ roots := by
  simp only [checkArgRoots, parameterAt, variableAt, refLike, annotation] at checked
  by_cases own : roots = [.param index]
  · exact Or.inl own
  · right
    by_cases included : arguments[index]?.getD [] ⊆ roots
    · exact included
    · cases tested : subsetRoots (arguments[index]?.getD []) roots with
      | false => simp [own, tested, Goose.Core.reject] at checked
      | true =>
        have members : ∀ root, root ∈ arguments[index]?.getD [] → root ∈ roots := by
          simpa [subsetRoots] using tested
        exact (included (fun {_} member => members _ member)).elim

private theorem rootCheck_bind_success {α β : Type} (action : Goose.Core.V α)
    (next : α → Goose.Core.V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem forAll_success_member {α : Type} (rows : List α) (action : α → Goose.Core.V Unit)
    (checked : Goose.Core.forAll rows action = .ok ()) : ∀ row ∈ rows, action row = .ok () := by
  induction rows with
  | nil => intro row absent; cases absent
  | cons row rows ih =>
    simp only [Goose.Core.forAll] at checked
    obtain ⟨value, first, rest⟩ := (rootCheck_bind_success _ _ _).mp checked
    cases value
    intro selected member
    rcases List.mem_cons.mp member with equal | member
    · subst selected
      exact first
    · exact ih rest selected member

theorem checkContent_variableRooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (environment : PEnv) (context : Context) (arguments : List Arg) (argumentRoots : List (List RootRef))
    (index holder : Nat) (mutability : Goose.Core.Mutability) (contents annotation : List RootRef) (value : Value)
    (contentAt : (context.contentRoots.find? (·.1 == index)).map Prod.snd = some contents)
    (argumentAt : arguments[index]? = some (.byRef mutability (.var holder)))
    (annotationAt : environment.ann holder = some annotation)
    (checked : checkContent environment context arguments argumentRoots index = .ok ())
    (rooted : DirectValueRooted caller annotation value) :
    DirectValueRooted (CallInterpretation caller callee argumentRoots) contents value := by
  unfold checkContent at checked
  simp only [contentAt] at checked
  obtain ⟨mapped, substituted, checked⟩ := (rootCheck_bind_success _ _ _).mp checked
  simp only [argumentAt, annotationAt] at checked
  have included : annotation ⊆ mapped := by
    cases covered : subsetRoots annotation mapped with
    | false => simp [covered, Goose.Core.reject, bind, Except.bind] at checked
    | true =>
      have members : ∀ root, root ∈ annotation → root ∈ mapped := by simpa [subsetRoots] using covered
      exact fun {_} member => members _ member
  intro location reference
  have reflected := mapResultRoots_reflects caller callee argumentRoots contents [] mapped substituted location.root
    (rootIn_mono included (rooted location reference))
  rcases reflected with ⟨symbolic, absent, _⟩ | actual
  · cases absent
  · exact actual

theorem checkContent_referenceRooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (environment : PEnv) (context : Context) (arguments : List Arg) (argumentRoots : List (List RootRef))
    (index holder : Nat) (mutability : Goose.Core.Mutability) (contents annotation : List RootRef) (value : Value)
    (contentAt : (context.contentRoots.find? (·.1 == index)).map Prod.snd = some contents)
    (argumentAt : arguments[index]? = some (.byRef mutability (.deref (.read (.var holder)))))
    (annotationAt : environment.cont holder = some annotation)
    (checked : checkContent environment context arguments argumentRoots index = .ok ())
    (rooted : DirectValueRooted caller annotation value) :
    DirectValueRooted (CallInterpretation caller callee argumentRoots) contents value := by
  unfold checkContent at checked
  simp only [contentAt] at checked
  obtain ⟨mapped, substituted, checked⟩ := (rootCheck_bind_success _ _ _).mp checked
  simp only [argumentAt, annotationAt] at checked
  have covered : (subsetRoots mapped annotation && subsetRoots annotation mapped) = true := by
    cases covered : subsetRoots mapped annotation && subsetRoots annotation mapped with
    | false => simp [covered, Goose.Core.reject] at checked
    | true => rfl
  have included : annotation ⊆ mapped := by
    have members : ∀ root, root ∈ annotation → root ∈ mapped := by
      simpa [subsetRoots] using ((Bool.and_eq_true _ _).mp covered).2
    exact fun {_} member => members _ member
  intro location reference
  have reflected := mapResultRoots_reflects caller callee argumentRoots contents [] mapped substituted location.root
    (rootIn_mono included (rooted location reference))
  rcases reflected with ⟨symbolic, absent, _⟩ | actual
  · cases absent
  · exact actual

theorem parameterAnnotation_external (module : Module) (implementation : Impl) (context : Context)
    (checked : checkAnnotationShape module implementation context = .ok ())
    (index : Nat) (bound : index < implementation.params.size) (roots : List RootRef)
    (annotated : (context.varRoots.find? (·.1 == index)).map Prod.snd = some roots) :
    ∀ root ∈ roots, match root with
      | .static | .global _ => True
      | .param position => position = index
      | .local _ => False := by
  unfold checkAnnotationShape at checked
  obtain ⟨_, _, checked⟩ := (rootCheck_bind_success _ _ _).mp checked
  obtain ⟨_, _, checked⟩ := (rootCheck_bind_success _ _ _).mp checked
  have parameter := forAll_success_member _ _ checked index (List.mem_range.mpr bound)
  cases selected : context.varRoots.find? (·.1 == index) with
  | none => simp [selected] at annotated
  | some entry =>
    have equal : entry.2 = roots := by simpa only [selected, Option.map_some, Option.some.injEq] using annotated
    simp only [selected] at parameter
    intro root member
    have accepted := forAll_success_member _ _ parameter root (equal ▸ member)
    cases root with
    | static => trivial
    | global id => trivial
    | «local» id => simp [Goose.Core.reject] at accepted
    | param position =>
      by_cases same : position = index
      · exact same
      · simp [same, Goose.Core.reject] at accepted

theorem checkArgRoots_parameterValueRooted (module : Module) (caller : RootInterpretation)
    (callee : RuntimeActivation) (implementation : Impl) (context : Context)
    (arguments : List (List RootRef)) (index : Nat) (parameter : Param) (descriptor : LocalVar)
    (annotation roots : List RootRef) (value : Value)
    (parameterAt : implementation.params[index]? = some parameter)
    (variableAt : implementation.vars[parameter.var]? = some descriptor)
    (parameterVariable : parameter.var = index) (refLike : descriptor.ty.isRefLike = true)
    (annotated : context.varRoots.find? (·.1 == parameter.var) = some (parameter.var, annotation))
    (checked : checkArgRoots implementation context arguments index = .ok ())
    (shaped : checkAnnotationShape module implementation context = .ok ())
    (argumentAt : arguments[index]? = some roots) (rooted : DirectValueRooted caller roots value) :
    DirectValueRooted (CallInterpretation caller callee arguments) annotation value := by
  have alternatives := checkArgRoots_annotation implementation context arguments index parameter descriptor annotation
    parameterAt variableAt refLike annotated checked
  have allowed := parameterAnnotation_external module implementation context shaped index
    (Array.getElem?_eq_some_iff.mp parameterAt).1 annotation (by rw [← parameterVariable, annotated]; rfl)
  intro location reference
  have sourceRoots := rooted location reference
  generalize actualRootEq : location.root = actualRoot at sourceRoots ⊢
  have sourceRooted := sourceRoots
  rcases alternatives with own | included
  · subst annotation
    exact ⟨.param index, by simp, .parameter index actualRoot ⟨roots, argumentAt, sourceRoots⟩⟩
  · obtain ⟨symbolic, member, actual⟩ := sourceRoots
    have member : symbolic ∈ annotation := included (by simpa only [argumentAt, Option.getD_some] using member)
    have external := allowed symbolic member
    cases symbolic with
    | static =>
      cases actual with
      | static id synthetic => exact ⟨.static, member, .static id synthetic⟩
    | global id =>
      cases actual with
      | global id declared => exact ⟨.global id, member, .global id declared⟩
    | «local» id => exact external.elim
    | param position =>
      subst position
      exact ⟨.param index, member, .parameter index actualRoot ⟨roots, argumentAt, sourceRooted⟩⟩

end Goose.Proofs.ConstructionRootCorrespondence
