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

end Goose.Proofs.ConstructionRootCorrespondence
