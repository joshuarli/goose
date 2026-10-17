import Goose.GIR.ReplacementContentFlowProofsNormalization
import Goose.GIR.ReplacementContentFlowProofsWrites

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem normalize_known_shape {f : Func} {roots : Roots} {actual : List RootRef}
    (known : normalize f roots = some actual) : ∃ atoms, roots = .known atoms := by
  cases roots <;> simp_all [normalize]

private theorem normalize_bind_fold_within (f : Func) (map : Atom → Roots)
    (atoms : List Atom) (upper : List RootRef)
    (mapped : ∀ atom ∈ atoms,
      ∃ actual, normalize f (map atom) = some actual ∧ actual ⊆ upper)
    (initial : Roots) (initialRoots : List RootRef)
    (initialKnown : normalize f initial = some initialRoots) (initialWithin : initialRoots ⊆ upper) :
    ∃ actual, normalize f (atoms.foldl (fun accumulated atom =>
      match accumulated, map atom with
      | .unknown, _ | _, .unknown => .unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) initial) = some actual ∧ actual ⊆ upper := by
  induction atoms generalizing initial initialRoots with
  | nil => exact ⟨initialRoots, initialKnown, initialWithin⟩
  | cons atom rest ih =>
      obtain ⟨nextRoots, nextKnown, nextWithin⟩ := mapped atom (by simp)
      obtain ⟨joinedRoots, joinedKnown, joinedWithin⟩ := normalize_join_known
        f initial (map atom) initialRoots nextRoots initialKnown nextKnown
      have mergedWithin : joinedRoots ⊆ upper := fun root member =>
        (joinedWithin root member).elim (fun included => initialWithin included) (fun included => nextWithin included)
      obtain ⟨initialAtoms, initialShape⟩ := normalize_known_shape initialKnown
      obtain ⟨mappedAtoms, mappedShape⟩ := normalize_known_shape nextKnown
      have equation : (fun accumulated next => match accumulated, map next with
          | .unknown, _ | _, .unknown => .unknown
          | .pending, _ | _, .pending => .pending
          | left, right => left.join right) initial atom = initial.join (map atom) := by
        simp only [initialShape, mappedShape]
      simpa only [List.foldl_cons, equation] using ih
        (fun next member => mapped next (List.mem_cons_of_mem atom member))
        (initial.join (map atom)) joinedRoots joinedKnown mergedWithin

theorem normalize_bind_known (f : Func) (atoms : List Atom) (map : Atom → Roots)
    (upper : List RootRef)
    (mapped : ∀ atom ∈ atoms,
      ∃ actual, normalize f (map atom) = some actual ∧ actual ⊆ upper) :
    ∃ actual, normalize f ((Roots.known atoms).bind map) = some actual ∧ actual ⊆ upper := by
  exact normalize_bind_fold_within f map atoms upper mapped (.known []) [] rfl (by simp)

theorem normalize_content_known (f : Func) (state : State) (addresses : List Atom)
    (upper : List RootRef)
    (localCells : ∀ slot, Atom.local slot ∈ addresses →
      ∃ actual, normalize f (flowAt state.slots slot) = some actual ∧ actual ⊆ upper)
    (parameterCells : ∀ index, Atom.param index ∈ addresses →
      (f.params[index]?).any Ty.isRefSlice = true ∧
      ∃ actual, normalize f (flowAt state.contents index) = some actual ∧ actual ⊆ upper)
    (addressShape : ∀ atom ∈ addresses, (∃ slot, atom = .local slot) ∨ ∃ index, atom = .param index) :
    ∃ actual, normalize f (content f state (.known addresses)) = some actual ∧ actual ⊆ upper := by
  apply normalize_bind_known
  intro atom member
  rcases addressShape atom member with ⟨slot, rfl⟩ | ⟨index, rfl⟩
  · exact localCells slot member
  · obtain ⟨reference, known⟩ := parameterCells index member
    simpa only [reference, ite_true] using known

theorem normalize_substitute_known (f : Func) (state : State) (args : List ValueId)
    (atoms : List Atom) (upper : List RootRef)
    (globals : ∀ global, Atom.global global ∈ atoms → RootRef.global global ∈ upper)
    (parameters : ∀ index, Atom.param index ∈ atoms →
      ∃ value actual, args[index]? = some value ∧
        normalize f (flowAt state.values value) = some actual ∧ actual ⊆ upper)
    (contents : ∀ index, Atom.contents index ∈ atoms →
      ∃ value actual, args[index]? = some value ∧
        normalize f (content f state (flowAt state.values value)) = some actual ∧ actual ⊆ upper)
    (external : ∀ slot, Atom.local slot ∉ atoms) :
    ∃ actual, normalize f (substitute f state args (.known atoms)) = some actual ∧ actual ⊆ upper := by
  apply normalize_bind_known
  intro atom member
  cases atom with
  | «local» slot => exact False.elim (external slot member)
  | global global =>
      refine ⟨[.global global], ?_, ?_⟩
      · rfl
      · intro root included
        have same : root = .global global := by simpa using included
        simpa only [same] using globals global member
  | param index =>
      obtain ⟨value, actual, argument, known, within⟩ := parameters index member
      exact ⟨actual, by simpa only [argument, Option.map_some, Option.getD_some] using known, within⟩
  | contents index =>
      obtain ⟨value, actual, argument, known, within⟩ := contents index member
      exact ⟨actual, by simpa only [argument, Option.map_some, Option.getD_some] using known, within⟩

def Roots.NormalizedWithin (observer : Func) (roots : Roots) (upper : List RootRef) : Prop :=
  roots = .pending ∨ ∃ actual, normalize observer roots = some actual ∧ actual ⊆ upper

theorem Roots.NormalizedWithin.pending (observer : Func) (upper : List RootRef) :
    Roots.pending.NormalizedWithin observer upper := Or.inl rfl

theorem Roots.NormalizedWithin.known_empty (observer : Func) (upper : List RootRef) :
    (Roots.known []).NormalizedWithin observer upper := Or.inr ⟨[], rfl, by simp⟩

theorem Roots.NormalizedWithin.not_unknown {observer : Func} {roots : Roots} {upper : List RootRef}
    (bounded : roots.NormalizedWithin observer upper) : roots ≠ .unknown := by
  intro same
  subst roots
  simp [Roots.NormalizedWithin, normalize] at bounded

theorem Roots.NormalizedWithin.actual {observer : Func} {roots : Roots} {upper : List RootRef}
    (bounded : roots.NormalizedWithin observer upper) (ready : roots ≠ .pending) :
    ∃ actual, normalize observer roots = some actual ∧ actual ⊆ upper :=
  bounded.resolve_left ready

theorem Roots.NormalizedWithin.mono {observer : Func} {roots : Roots} {upper wider : List RootRef}
    (bounded : roots.NormalizedWithin observer upper) (within : upper ⊆ wider) :
    roots.NormalizedWithin observer wider := by
  rcases bounded with pending | ⟨actual, known, valid⟩
  · exact Or.inl pending
  · exact Or.inr ⟨actual, known, fun _ member => within (valid member)⟩

theorem Roots.NormalizedWithin.join {observer : Func} {left right : Roots} {upper : List RootRef}
    (leftBound : left.NormalizedWithin observer upper)
    (rightBound : right.NormalizedWithin observer upper) :
    (left.join right).NormalizedWithin observer upper := by
  rcases leftBound with pending | ⟨leftRoots, leftKnown, leftWithin⟩
  · subst left
    have identity : Roots.pending.join right = right := by cases right <;> rfl
    rwa [identity]
  · rcases rightBound with pending | ⟨rightRoots, rightKnown, rightWithin⟩
    · subst right
      have identity : left.join Roots.pending = left := by cases left <;> rfl
      rw [identity]
      exact Or.inr ⟨leftRoots, leftKnown, leftWithin⟩
    · obtain ⟨actual, known, within⟩ := normalize_join_known observer left right
        leftRoots rightRoots leftKnown rightKnown
      exact Or.inr ⟨actual, known, fun root member =>
        (within root member).elim (fun included => leftWithin included) (fun included => rightWithin included)⟩

private theorem normalizedWithin_strictMerge (observer : Func) (left right : Roots)
    (upper : List RootRef) (leftBound : left.NormalizedWithin observer upper)
    (rightBound : right.NormalizedWithin observer upper) :
    ((fun (left right : Roots) => match left, right with
      | .unknown, _ | _, .unknown => Roots.unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) left right).NormalizedWithin observer upper := by
  have leftSafe := leftBound.not_unknown
  have rightSafe := rightBound.not_unknown
  cases left with
  | unknown => exact False.elim (leftSafe rfl)
  | pending =>
      cases right with
      | unknown => exact False.elim (rightSafe rfl)
      | pending | known => exact Or.inl rfl
  | known left =>
      cases right with
      | unknown => exact False.elim (rightSafe rfl)
      | pending => exact Or.inl rfl
      | known right => exact leftBound.join rightBound

theorem Roots.NormalizedWithin.bind_known (observer : Func) (atoms : List Atom)
    (map : Atom → Roots) (upper : List RootRef)
    (mapped : ∀ atom ∈ atoms, (map atom).NormalizedWithin observer upper) :
    ((Roots.known atoms).bind map).NormalizedWithin observer upper := by
  dsimp only [Roots.bind]
  apply List.foldlRecOn (motive := fun (roots : Roots) => roots.NormalizedWithin observer upper)
    atoms _ (Roots.NormalizedWithin.known_empty observer upper)
  intro current bounded atom member
  exact normalizedWithin_strictMerge observer current (map atom) upper bounded (mapped atom member)

theorem Roots.NormalizedWithin.content_known (observer f : Func) (state : State)
    (addresses : List Atom) (upper : List RootRef)
    (localCells : ∀ slot, Atom.local slot ∈ addresses →
      (flowAt state.slots slot).NormalizedWithin observer upper)
    (parameterCells : ∀ index, Atom.param index ∈ addresses →
      (f.params[index]?).any Ty.isRefSlice = true ∧
      (flowAt state.contents index).NormalizedWithin observer upper)
    (addressShape : ∀ atom ∈ addresses, (∃ slot, atom = .local slot) ∨ ∃ index, atom = .param index) :
    (content f state (.known addresses)).NormalizedWithin observer upper := by
  apply Roots.NormalizedWithin.bind_known
  intro atom member
  rcases addressShape atom member with ⟨slot, rfl⟩ | ⟨index, rfl⟩
  · exact localCells slot member
  · obtain ⟨reference, known⟩ := parameterCells index member
    simpa only [reference, ite_true] using known

theorem Roots.NormalizedWithin.substitute_known (observer f : Func) (state : State)
    (args : List ValueId) (atoms : List Atom) (upper : List RootRef)
    (globals : ∀ global, Atom.global global ∈ atoms → RootRef.global global ∈ upper)
    (parameters : ∀ index, Atom.param index ∈ atoms →
      ∃ value, args[index]? = some value ∧
        (flowAt state.values value).NormalizedWithin observer upper)
    (contents : ∀ index, Atom.contents index ∈ atoms →
      ∃ value, args[index]? = some value ∧
        (content f state (flowAt state.values value)).NormalizedWithin observer upper)
    (external : ∀ slot, Atom.local slot ∉ atoms) :
    (substitute f state args (.known atoms)).NormalizedWithin observer upper := by
  apply Roots.NormalizedWithin.bind_known
  intro atom member
  cases atom with
  | «local» slot => exact False.elim (external slot member)
  | global global =>
      refine Or.inr ⟨[.global global], rfl, ?_⟩
      intro root included
      have same : root = .global global := by simpa using included
      simpa only [same] using globals global member
  | param index =>
      obtain ⟨value, argument, bounded⟩ := parameters index member
      simpa only [argument, Option.map_some, Option.getD_some] using bounded
  | contents index =>
      obtain ⟨value, argument, bounded⟩ := contents index member
      simpa only [argument, Option.map_some, Option.getD_some] using bounded

#print axioms normalize_bind_known
#print axioms normalize_content_known
#print axioms Roots.NormalizedWithin.content_known
#print axioms Roots.NormalizedWithin.substitute_known
#print axioms Roots.NormalizedWithin.join
#print axioms Roots.NormalizedWithin.bind_known
#print axioms Roots.NormalizedWithin.actual
#print axioms normalize_substitute_known

end Goose.GIR.ReplacementContentFlow.Model
