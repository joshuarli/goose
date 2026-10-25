import Goose.GIR.ReplacementContentFlowProofsSliceTouchReachable

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

structure CallObservationReady (callee func : Func) (state : State) (args : List ValueId) : Prop where
  arguments : ∀ index, index < callee.params.length → ∃ value roots,
    args[index]? = some value ∧ normalize func (flowAt state.values value) = some roots
  contents : ∀ index row, index < callee.params.length →
    callee.roots.contents.find? (·.1 == index) = some (index,row) → ∃ value roots,
      args[index]? = some value ∧ normalize func (content func state (flowAt state.values value)) = some roots

def SliceOrigin (func : Func) (observed : List Atom) (atom : Atom) : Prop :=
  atom ∈ observed ∨ ∃ index mutability element,
    atom = .param index ∧ func.params[index]? = some (.slice mutability element)

theorem publicTouches_known (atoms : List Atom) : ∃ output, publicTouches (.known atoms) = .known output := by
  apply Roots.bind_all_known
  intro atom _
  cases atom <;> exact ⟨_,rfl⟩

theorem publicTouches_member {atoms exposed : List Atom} (known : publicTouches (.known atoms) = .known exposed)
    {atom : Atom} (member : atom ∈ atoms) (external : ∀ slot, atom ≠ .local slot) : atom ∈ exposed := by
  have mapped := Roots.bind_known_maps known atom member
  cases atom with
  | «local» slot => exact False.elim (external slot rfl)
  | global global | param index | contents index =>
      all_goals obtain ⟨roots,rootsAt,within⟩ := mapped
      all_goals cases rootsAt
      all_goals exact within (by simp)

theorem substitute_public_known {module : Module} {callee func : Func} {state : State}
    {args : List ValueId} {atoms : List Atom}
    (normalizable : (Roots.known atoms).AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (supported : (Roots.known atoms).Supported (atomUniverse module callee))
    (available : CallObservationReady callee func state args) :
    ∃ exposed output, publicTouches (.known atoms) = .known exposed ∧
      substitute func state args (.known exposed) = .known output := by
  obtain ⟨exposed,publicAt⟩ := publicTouches_known atoms
  suffices ∃ output, substitute func state args (.known exposed) = .known output by
    obtain ⟨output,outputAt⟩ := this
    exact ⟨exposed,output,publicAt,outputAt⟩
  have rows := publicTouches_normalizableAtoms normalizable
  rw [publicAt] at rows
  have publicSupport := publicTouches_supported supported
  rw [publicAt] at publicSupport
  apply Roots.bind_all_known
  intro atom member
  cases atom with
  | «local» slot => exact False.elim ((rows _ member).2 slot rfl)
  | global global => exact ⟨_,rfl⟩
  | param index =>
      obtain ⟨value,actual,argument,known⟩ := available.arguments index
        ((atomUniverse_param module callee index).mp (publicSupport.2 member))
      obtain ⟨roots,rootsAt⟩ := normalize_known_shape known
      exact ⟨roots,by simpa only [argument,Option.map_some,Option.getD_some] using rootsAt⟩
  | contents index =>
      cases annotation : callee.roots.contents.find? (·.1 == index) with
      | none => simpa [normalizeAtom,annotation] using (rows _ member).1
      | some row =>
          have selection := Array.find?_some annotation
          have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
          rcases row with ⟨selected,ceiling⟩
          change selected = index at identity
          subst selected
          obtain ⟨value,actual,argument,known⟩ := available.contents index ceiling
            ((atomUniverse_contents module callee index).mp (publicSupport.2 member)) annotation
          obtain ⟨roots,rootsAt⟩ := normalize_known_shape known
          exact ⟨roots,by simpa only [argument,Option.map_some,Option.getD_some] using rootsAt⟩

theorem substitute_slice_origins {module : Module} {callee func : Func}
    {before final : State} {args : List ValueId} {roots : Roots} {touches : List Atom}
    {predicate : Atom → Prop}
    (growth : before.Extends final)
    (origins : roots.AtomsWithin (SliceOrigin callee touches))
    (external : roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (rootSupport : roots.Supported (atomUniverse module callee))
    (touchRows : (Roots.known touches).AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (touchSupport : (Roots.known touches).Supported (atomUniverse module callee))
    (available : CallObservationReady callee func final args)
    (observed : (substitute func final args (publicTouches (.known touches))).AtomsWithin predicate)
    (parameters : ∀ (index : Nat) (mutability : Mutability) (element : Ty), callee.params[index]? = some (.slice mutability element) →
      ∀ argument, args[index]? = some argument → (flowAt before.values argument).AtomsWithin predicate) :
    (substitute func before args roots).AtomsWithin predicate := by
  obtain ⟨exposed,output,publicAt,outputAt⟩ := substitute_public_known touchRows touchSupport available
  have outputBound : (Roots.known output).AtomsWithin predicate := by
    simpa only [publicAt,outputAt] using observed
  cases roots with
  | pending => trivial
  | unknown => exact False.elim origins
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      rcases origins atom member with touched | ⟨index,mutability,element,same,formal⟩
      · have exposedMember := publicTouches_member publicAt touched (external atom member)
        have mapped := Roots.AtomsWithin.bind_atom outputAt outputBound exposedMember
        cases atom with
        | «local» slot => exact False.elim (external _ member slot rfl)
        | global global => exact mapped
        | param index =>
            cases argument : args[index]? with
            | none => simp only [argument,Option.map_none,Option.getD_none,Roots.AtomsWithin] at mapped
            | some value =>
                simp only [argument,Option.map_some,Option.getD_some] at mapped ⊢
                exact (growth.values.values value).atomsWithin mapped
        | contents index =>
            cases annotation : callee.roots.contents.find? (·.1 == index) with
            | none => simpa [normalizeAtom,annotation] using touchRows _ touched
            | some row =>
                have selection := Array.find?_some annotation
                have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
                rcases row with ⟨selected,ceiling⟩
                change selected = index at identity
                subst selected
                obtain ⟨value,actual,argument,known⟩ := available.contents index ceiling
                  ((atomUniverse_contents module callee index).mp (rootSupport.2 member)) annotation
                simp only [argument,Option.map_some,Option.getD_some] at mapped ⊢
                apply content_atomsWithin_of_extends growth (growth.values.values value) mapped
                intro pending
                change normalize func (content func final (flowAt final.values value)) = some actual at known
                change content func final (flowAt final.values value) = .pending at pending
                rw [pending] at known
                cases known
      · subst atom
        cases argument : args[index]? with
        | none =>
            have indexBound := (atomUniverse_param module callee index).mp (rootSupport.2 member)
            obtain ⟨value,_,argumentAt,_⟩ := available.arguments index indexBound
            simp [argument] at argumentAt
        | some value =>
            simp only [argument,Option.map_some,Option.getD_some]
            exact parameters index mutability element formal value argument

theorem substitute_slice_origins_final {module : Module} {callee func : Func}
    {before final : State} {args : List ValueId} {roots : Roots} {touches : List Atom}
    {predicate : Atom → Prop}
    (growth : before.Extends final)
    (origins : roots.AtomsWithin (SliceOrigin callee touches))
    (external : roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (rootSupport : roots.Supported (atomUniverse module callee))
    (touchRows : (Roots.known touches).AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (touchSupport : (Roots.known touches).Supported (atomUniverse module callee))
    (available : CallObservationReady callee func final args)
    (observed : (substitute func final args (publicTouches (.known touches))).AtomsWithin predicate)
    (parameters : ∀ (index : Nat) (mutability : Mutability) (element : Ty), callee.params[index]? = some (.slice mutability element) →
      ∀ argument, args[index]? = some argument → (flowAt final.values argument).AtomsWithin predicate) :
    (substitute func before args roots).AtomsWithin predicate := by
  exact substitute_slice_origins growth origins external rootSupport touchRows touchSupport available observed
    (fun index mutability element formal argument actual =>
      (growth.values.values argument).atomsWithin (parameters index mutability element formal argument actual))

#print axioms publicTouches_member
#print axioms substitute_public_known

end Goose.GIR.ReplacementContentFlow.Model
