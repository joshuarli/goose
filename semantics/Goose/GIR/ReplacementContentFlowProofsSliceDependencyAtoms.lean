import Goose.GIR.ReplacementContentFlowProofsSliceReachable
import Goose.GIR.ReplacementContentFlowProofsCallArgumentObservation

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def OwnerDependencyAtom (module : Module) (func : Func) (upper : List RootRef) (atom : Atom) : Prop :=
  ∃ roots, ownerDependencies module func (.known [atom]) = some roots ∧ roots ⊆ upper

theorem ownerDependencies_atomsWithin {module : Module} {func : Func} {roots : Roots} {actual : List RootRef}
    (known : ownerDependencies module func roots = some actual) :
    roots.AtomsWithin (OwnerDependencyAtom module func actual) := by
  cases roots with
  | pending => simp [ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
  | unknown => simp [ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
  | known atoms =>
      intro atom member
      exact ownerDependencies_known_subset (by simpa using member : [atom] ⊆ atoms) known

theorem OwnerDependencyAtom.mono {module : Module} {func : Func} {before after : List RootRef} {atom : Atom}
    (bounded : OwnerDependencyAtom module func before atom) (within : before ⊆ after) :
    OwnerDependencyAtom module func after atom := by
  obtain ⟨roots,known,bounded⟩ := bounded
  exact ⟨roots,known,fun _ member => within (bounded member)⟩

theorem rawOwnerTouches_singleton (module : Module) (atom : Atom) :
    rawOwnerTouches module (.known [atom]) = match atom with
      | .global global => .known ((ownerTouches module [.global global]).map Atom.ofRootRef)
      | atom => .known [atom] := by
  cases atom with
  | «local» slot | param index | contents index => rfl
  | global global =>
      change rawOwnerTouches module (.known [.global global]) =
        .known ((ownerTouches module [.global global]).map Atom.ofRootRef)
      by_cases closed : storageClosed module = true
      · cases retained : (module.globals[global]?).all (fun global => global.ty.ownerElem?.isSome) <;>
          simp [rawOwnerTouches,ownerTouches,closed,retained,Roots.bind,Roots.join,Atom.ofRootRef]
      · simp [rawOwnerTouches,ownerTouches,closed,Roots.bind,Roots.join,Atom.ofRootRef]

theorem ownerDependencies_of_atomsWithin {module : Module} {func : Func} {roots : Roots} {upper : List RootRef}
    (bounded : roots.AtomsWithin (OwnerDependencyAtom module func upper)) (ready : roots ≠ .pending) :
    ∃ actual, ownerDependencies module func roots = some actual ∧ actual ⊆ upper := by
  cases roots with
  | pending => exact False.elim (ready rfl)
  | unknown => exact False.elim bounded
  | known atoms =>
      apply normalize_bind_known
      intro atom member
      obtain ⟨actual,known,within⟩ := bounded atom member
      unfold ownerDependencies at known
      rw [rawOwnerTouches_singleton] at known
      exact ⟨actual,known,within⟩

theorem ownerDependencies_within_of_atomsWithin {module : Module} {func : Func} {roots : Roots}
    {actual upper : List RootRef}
    (bounded : roots.AtomsWithin (OwnerDependencyAtom module func upper))
    (known : ownerDependencies module func roots = some actual) : actual ⊆ upper := by
  have ready : roots ≠ .pending := by
    intro same
    simp [same,ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
  obtain ⟨produced,producedAt,within⟩ := ownerDependencies_of_atomsWithin bounded ready
  have same : produced = actual := Option.some.inj (producedAt.symm.trans known)
  simpa only [same] using within

#print axioms rawOwnerTouches_singleton
#print axioms ownerDependencies_within_of_atomsWithin

end Goose.GIR.ReplacementContentFlow.Model
