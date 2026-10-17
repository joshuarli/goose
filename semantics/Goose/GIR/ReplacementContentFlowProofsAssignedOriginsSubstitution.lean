import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsWrites

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private theorem strict_fold_nonpending (atoms : List Atom) (map : Atom → Roots)
    (mapped : ∀ atom ∈ atoms, map atom ≠ .pending)
    (initial : Roots) (ready : initial ≠ .pending) :
    atoms.foldl (fun accumulated atom => match accumulated, map atom with
      | .unknown, _ | _, .unknown => .unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) initial ≠ .pending := by
  induction atoms generalizing initial with
  | nil => exact ready
  | cons atom atoms ih =>
    apply ih (fun next member => mapped next (List.mem_cons_of_mem atom member))
    have current := mapped atom (by simp)
    cases initial <;> cases mappedRoot : map atom <;> simp_all [Roots.join]

theorem Roots.bind_nonpending {roots : Roots} {map : Atom → Roots}
    (ready : roots ≠ .pending)
    (mapped : ∀ atoms, roots = .known atoms → ∀ atom ∈ atoms, map atom ≠ .pending) :
    roots.bind map ≠ .pending := by
  cases roots with
  | pending => exact False.elim (ready rfl)
  | unknown => simp [Roots.bind]
  | known atoms => exact strict_fold_nonpending atoms map (mapped atoms rfl) (.known []) (by simp)

theorem substitute_nonpending (func : Func) (state : State) (arguments : List ValueId)
    (roots : Roots) (ready : roots ≠ .pending)
    (parameters : ∀ atoms, roots = .known atoms → ∀ index, .param index ∈ atoms →
      ∀ value, arguments[index]? = some value → flowAt state.values value ≠ .pending)
    (contents : ∀ atoms, roots = .known atoms → ∀ index, .contents index ∈ atoms →
      ∀ value, arguments[index]? = some value →
        content func state (flowAt state.values value) ≠ .pending) :
    substitute func state arguments roots ≠ .pending := by
  apply Roots.bind_nonpending ready
  intro atoms same atom member
  cases atom with
  | «local» slot => simp
  | global global => simp
  | param index =>
    cases found : arguments[index]? with
    | none => simp [found]
    | some value => simpa [found] using parameters atoms same index member value found
  | contents index =>
    cases found : arguments[index]? with
    | none => simp [found]
    | some value => simpa [found] using contents atoms same index member value found

theorem Roots.Extends.known_member {before after : Roots} (growth : before.Extends after)
    (safe : after ≠ .unknown) {atoms : List Atom} (known : before = .known atoms)
    {atom : Atom} (member : atom ∈ atoms) :
    ∃ nextAtoms, after = .known nextAtoms ∧ atom ∈ nextAtoms := by
  subst before
  cases after with
  | pending => simp [Roots.Extends] at growth
  | unknown => exact False.elim (safe rfl)
  | known nextAtoms => exact ⟨nextAtoms, rfl, growth.subset member⟩

#print axioms substitute_nonpending
#print axioms Roots.Extends.known_member

end Goose.GIR.ReplacementContentFlow.Model
