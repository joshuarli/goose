import Goose.GIR.RootBoundsRefinement
import Goose.GIR.ReplacementContentFlowProofsTransfer
import Goose.GIR.ReplacementContentFlowProofsRefinement

namespace Goose.GIR

open Goose.Core

theorem RootsRefine.union {func : Func} {left right source : List RootRef}
    (leftBound : RootsRefine func left source) (rightBound : RootsRefine func right source) :
    RootsRefine func (unionRoots left right) source := by
  intro root member
  exact (ReplacementContentFlow.Model.unionRoots_mem_iff _ _ _).mp member |>.elim
    (leftBound root) (rightBound root)

namespace ReplacementContentFlow.Model

def symbolicRoots (func : Func) (roots : Roots) : Option (List RootRef) :=
  normalize { func with roots := { func.roots with params := #[] } } roots

private theorem unspecialized_expand (func : Func) (root : RootRef) :
    ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot root = [root] := by
  cases root <;> simp [Func.expandParameterRoot, Func.parameterRoots]

private theorem unspecialized_flatMap (func : Func) (roots : List RootRef) :
    roots.flatMap ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot = roots := by
  have identity : ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot =
      fun root => [root] := funext (unspecialized_expand func)
  rw [identity]
  simp

private theorem normalizeAtom_symbolic (func : Func) (atom : Atom) :
    normalizeAtom func atom =
      (normalizeAtom { func with roots := { func.roots with params := #[] } } atom).map
        (·.flatMap func.expandParameterRoot) := by
  cases atom with
  | «local» slot => simp [normalizeAtom, Func.expandParameterRoot]
  | global global => simp [normalizeAtom, Func.expandParameterRoot]
  | param index => simp [normalizeAtom, Func.expandParameterRoot, Func.parameterRoots]
  | contents index =>
    cases found : func.roots.contents.find? (·.1 == index) with
    | none => simp [normalizeAtom, found]
    | some row =>
      simp only [normalizeAtom, found, Option.map_some]
      change some (row.2.flatMap func.expandParameterRoot) =
        some ((row.2.flatMap ({ func with roots := { func.roots with params := #[] } } : Func).expandParameterRoot).flatMap func.expandParameterRoot)
      rw [unspecialized_flatMap]

theorem symbolicRoots_parameter (func : Func) (index : Nat) :
    symbolicRoots func (.known [.param index]) = some [.param index] := by
  simp [symbolicRoots, normalize, normalizeAtom, Func.parameterRoots, unionRoots]

theorem symbolicRoots_actual_within {func : Func} {roots : Roots} {symbolic : List RootRef}
    (known : symbolicRoots func roots = some symbolic) :
    ∃ actual, normalize func roots = some actual ∧
      ∀ root ∈ actual, root ∈ symbolic.flatMap func.expandParameterRoot := by
  cases roots with
  | pending => simp [symbolicRoots, normalize] at known
  | unknown => simp [symbolicRoots, normalize] at known
  | known atoms =>
    have atomBounds := (normalize_fold_atoms _ atoms [] symbolic known).2
    obtain ⟨actual, normalized, within⟩ := normalize_fold_within func atoms
      (symbolic.flatMap func.expandParameterRoot) (by
        intro atom member
        obtain ⟨raw, rawKnown, rawWithin⟩ := atomBounds atom member
        refine ⟨raw.flatMap func.expandParameterRoot, ?_, ?_⟩
        · rw [normalizeAtom_symbolic, rawKnown]
          rfl
        · intro root included
          obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp included
          exact List.mem_flatMap.mpr ⟨sourceRoot, rawWithin sourceMember, expanded⟩) [] (by simp)
    exact ⟨actual, normalized, within⟩


theorem symbolicRoots_contents {func : Func} {index : Nat} {roots : List RootRef}
    (annotation : func.roots.contents.find? (·.1 == index) = some (index, roots)) :
    symbolicRoots func (.known [.contents index]) = some (unionRoots [] roots) := by
  simp [symbolicRoots, normalize, normalizeAtom, annotation, unspecialized_flatMap]

theorem symbolicAtom_contents {func : Func} {index : Nat} {roots : List RootRef}
    (annotation : func.roots.contents.find? (·.1 == index) = some (index, roots)) :
    normalizeAtom { func with roots := { func.roots with params := #[] } } (.contents index) = some roots := by
  simp only [normalizeAtom,annotation,Option.map_some,unspecialized_flatMap]

def SymbolicRootsRefine (func : Func) (roots : Roots) (source : List RootRef) : Prop :=
  roots = .pending ∨ ∃ actual, symbolicRoots func roots = some actual ∧ RootsRefine func actual source

theorem SymbolicRootsRefine.pending (func : Func) (source : List RootRef) :
    SymbolicRootsRefine func .pending source := Or.inl rfl

theorem SymbolicRootsRefine.source_mono {func : Func} {roots : Roots} {source larger : List RootRef}
    (bounded : SymbolicRootsRefine func roots source) (within : source ⊆ larger) :
    SymbolicRootsRefine func roots larger := by
  rcases bounded with pending | ⟨actual, known, refined⟩
  · exact Or.inl pending
  · exact Or.inr ⟨actual, known, refined.source_mono (fun _ member => within member)⟩

theorem SymbolicRootsRefine.join {func : Func} {left right : Roots} {source : List RootRef}
    (leftBound : SymbolicRootsRefine func left source)
    (rightBound : SymbolicRootsRefine func right source) :
    SymbolicRootsRefine func (left.join right) source := by
  rcases leftBound with pending | ⟨leftRoots, leftKnown, leftRefined⟩
  · subst left
    have same : Roots.pending.join right = right := by cases right <;> rfl
    rwa [same]
  · rcases rightBound with pending | ⟨rightRoots, rightKnown, rightRefined⟩
    · subst right
      have same : left.join Roots.pending = left := by cases left <;> rfl
      rw [same]
      exact Or.inr ⟨leftRoots, leftKnown, leftRefined⟩
    · obtain ⟨actual, known, within⟩ := normalize_join_known
        { func with roots := { func.roots with params := #[] } } left right
        leftRoots rightRoots leftKnown rightKnown
      refine Or.inr ⟨actual, known, ?_⟩
      intro root member
      exact (within root member).elim (leftRefined root) (rightRefined root)

theorem SymbolicRootsRefine.actual {func : Func} {roots : Roots} {source : List RootRef}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global) (bounded : SymbolicRootsRefine func roots source)
    (ready : roots ≠ .pending) :
    ∃ actual, normalize func roots = some actual ∧
      actual ⊆ source.flatMap func.expandParameterRoot := by
  obtain ⟨symbolic, known, refined⟩ := bounded.resolve_left ready
  obtain ⟨actual, actualKnown, within⟩ := symbolicRoots_actual_within known
  refine ⟨actual, actualKnown, ?_⟩
  intro root member
  obtain ⟨symbol, symbolMember, expanded⟩ := List.mem_flatMap.mp (within root member)
  exact refined.expanded closed symbol symbolMember root expanded

theorem SymbolicRootsRefine.global_iff (func : Func) (global : GlobalId) (source : List RootRef) :
    SymbolicRootsRefine func (.known [.global global]) source ↔ RootRef.global global ∈ source := by
  have known : symbolicRoots func (.known [.global global]) = some [.global global] := rfl
  simp [SymbolicRootsRefine, known, RootsRefine, Func.expandParameterRoot]

theorem SymbolicRootsRefine.parameter_iff (func : Func) (index : Nat) (source : List RootRef) :
    SymbolicRootsRefine func (.known [.param index]) source ↔
      RootRef.param index ∈ source ∨ func.parameterRoots index ⊆ source := by
  simp [SymbolicRootsRefine, symbolicRoots_parameter, RootsRefine, Func.expandParameterRoot,
    List.subset_def]

theorem SymbolicRootsRefine.contents {func : Func} {index : Nat} {source : List RootRef}
    (row : func.roots.contents.find? (·.1 == index) = some (index, source)) :
    SymbolicRootsRefine func (.known [.contents index]) source := by
  refine Or.inr ⟨unionRoots [] source, symbolicRoots_contents row, ?_⟩
  intro root member
  exact Or.inl (((unionRoots_mem_iff _ _ _).mp member).resolve_left (by simp))

theorem SymbolicRootsRefine.rootMap (func : Func) (source : List RootRef) :
    SymbolicRootsRefine func (.known (source.eraseDups.map Atom.ofRootRef)) source := by
  let observer : Func := { func with roots := { func.roots with params := #[] } }
  have expansion : observer.expandParameterRoot = fun root => [root] := by
    funext root
    cases root <;> simp [observer, Func.expandParameterRoot, Func.parameterRoots]
  obtain ⟨actual, known, members⟩ := normalize_rootMap_dedup_known observer source
  refine Or.inr ⟨actual, known, ?_⟩
  intro root member
  apply Or.inl
  have literal := (members root).mp member
  simpa [expansion] using literal

theorem SymbolicRootsRefine.known_empty (func : Func) (source : List RootRef) :
    SymbolicRootsRefine func (.known []) source :=
  Or.inr ⟨[], rfl, fun _ member => False.elim (List.not_mem_nil member)⟩

theorem SymbolicRootsRefine.not_unknown {func : Func} {roots : Roots} {source : List RootRef}
    (bounded : SymbolicRootsRefine func roots source) : roots ≠ .unknown := by
  intro same
  subst roots
  simp [SymbolicRootsRefine, symbolicRoots, normalize] at bounded

theorem SymbolicRootsRefine.refine {func : Func} {roots : Roots} {source larger : List RootRef}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (bounded : SymbolicRootsRefine func roots source) (within : RootsRefine func source larger) :
    SymbolicRootsRefine func roots larger := by
  rcases bounded with pending | ⟨actual, known, refined⟩
  · exact Or.inl pending
  · exact Or.inr ⟨actual, known, refined.trans closed within⟩

private theorem symbolicRootsRefine_strictMerge (func : Func) (left right : Roots)
    (source : List RootRef) (leftBound : SymbolicRootsRefine func left source)
    (rightBound : SymbolicRootsRefine func right source) :
    ((fun (left right : Roots) => match left, right with
      | .unknown, _ | _, .unknown => Roots.unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) left right) |> fun roots =>
        SymbolicRootsRefine func roots source := by
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

theorem SymbolicRootsRefine.bind_known (func : Func) (atoms : List Atom)
    (map : Atom → Roots) (source : List RootRef)
    (mapped : ∀ atom ∈ atoms, SymbolicRootsRefine func (map atom) source) :
    SymbolicRootsRefine func ((Roots.known atoms).bind map) source := by
  dsimp only [Roots.bind]
  apply List.foldlRecOn (motive := fun roots => SymbolicRootsRefine func roots source)
    atoms _ (SymbolicRootsRefine.known_empty func source)
  intro current bounded atom member
  exact symbolicRootsRefine_strictMerge func current (map atom) source bounded (mapped atom member)

theorem Roots.Extends.symbolicRootsRefine {func : Func} {before after : Roots}
    {source : List RootRef} (growth : before.Extends after)
    (bounded : SymbolicRootsRefine func after source) :
    SymbolicRootsRefine func before source := by
  cases before with
  | pending => exact Or.inl rfl
  | unknown =>
      cases after <;> simp_all [Roots.Extends, SymbolicRootsRefine, symbolicRoots, normalize]
  | known before =>
      cases after with
      | pending => simp [Roots.Extends] at growth
      | unknown => exact False.elim (bounded.not_unknown rfl)
      | known after =>
          obtain ⟨actual, known, within⟩ := bounded.resolve_left (by simp)
          have atoms := (normalize_fold_atoms _ after [] actual known).2
          obtain ⟨result, normalized, valid⟩ := normalize_fold_within
            { func with roots := { func.roots with params := #[] } } before actual (by
              intro atom member
              exact atoms atom (growth.subset member)) [] (by simp)
          exact Or.inr ⟨result, normalized, within.actual_mono valid⟩

theorem normalize_known_members {func : Func} {atoms : List Atom} {actual : List RootRef}
    (known : normalize func (.known atoms) = some actual) (root : RootRef) :
    root ∈ actual ↔ ∃ atom ∈ atoms, ∃ mapped,
      normalizeAtom func atom = some mapped ∧ root ∈ mapped := by
  have atomKnowledge := (normalize_fold_atoms func atoms [] actual known).2
  let upper := atoms.flatMap fun atom => (normalizeAtom func atom).getD []
  obtain ⟨computed, normalized, within⟩ := normalize_fold_within func atoms upper (by
    intro atom member
    obtain ⟨mapped, mappedKnown, _⟩ := atomKnowledge atom member
    refine ⟨mapped, mappedKnown, ?_⟩
    intro current included
    apply List.mem_flatMap.mpr
    exact ⟨atom, member, by simpa [mappedKnown] using included⟩) [] (by simp)
  have same : computed = actual := Option.some.inj (normalized.symm.trans known)
  subst computed
  constructor
  · intro member
    obtain ⟨atom, atomMember, rootMember⟩ := List.mem_flatMap.mp (within member)
    obtain ⟨mapped, mappedKnown, _⟩ := atomKnowledge atom atomMember
    exact ⟨atom, atomMember, mapped, mappedKnown, by simpa [mappedKnown] using rootMember⟩
  · rintro ⟨atom, atomMember, mapped, mappedKnown, rootMember⟩
    obtain ⟨prior, priorKnown, priorWithin⟩ := atomKnowledge atom atomMember
    have same := Option.some.inj (priorKnown.symm.trans mappedKnown)
    subst prior
    exact priorWithin rootMember

theorem SymbolicRootsRefine.local_not_mem {func : Func} {atoms : List Atom} {source : List RootRef}
    (bounded : SymbolicRootsRefine func (.known atoms) source)
    (external : ∀ slot, RootRef.local slot ∉ source) (slot : SlotId) : Atom.local slot ∉ atoms := by
  obtain ⟨actual,known,refined⟩ := bounded.resolve_left (by simp)
  intro member
  have actualMember := (normalize_known_members known (.local slot)).mpr
    ⟨.local slot,member,[.local slot],rfl,by simp⟩
  rcases refined (.local slot) actualMember with literal | expanded
  · exact external slot literal
  · exact external slot (expanded _ (by simp [Func.expandParameterRoot]))

theorem symbolicRoots_actual_members {func : Func} {roots : Roots} {symbolic actual : List RootRef}
    (symbolicKnown : symbolicRoots func roots = some symbolic)
    (actualKnown : normalize func roots = some actual) (root : RootRef) :
    root ∈ actual ↔ root ∈ symbolic.flatMap func.expandParameterRoot := by
  obtain ⟨atoms, rfl⟩ := normalize_known_shape actualKnown
  constructor
  · intro member
    obtain ⟨computed, computedKnown, within⟩ := symbolicRoots_actual_within symbolicKnown
    have same := Option.some.inj (computedKnown.symm.trans actualKnown)
    subst computed
    exact within root member
  · intro member
    obtain ⟨symbol, symbolMember, expanded⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, atomMember, mapped, mappedKnown, literal⟩ :=
      (normalize_known_members symbolicKnown symbol).mp symbolMember
    have actualAtom : normalizeAtom func atom = some (mapped.flatMap func.expandParameterRoot) := by
      rw [normalizeAtom_symbolic, mappedKnown]
      rfl
    exact (normalize_known_members actualKnown root).mpr
      ⟨atom, atomMember, _, actualAtom, List.mem_flatMap.mpr ⟨symbol, literal, expanded⟩⟩

theorem SymbolicRootsRefine.of_normalized {func : Func} {roots : Roots}
    {actual source : List RootRef}
    (symbolicKnown : (symbolicRoots func roots).isSome = true)
    (actualKnown : normalize func roots = some actual)
    (within : actual ⊆ source) :
    SymbolicRootsRefine func roots source := by
  obtain ⟨symbolic, known⟩ := Option.isSome_iff_exists.mp symbolicKnown
  refine Or.inr ⟨symbolic, known, ?_⟩
  intro root member
  refine Or.inr ?_
  intro concrete concreteMember
  exact within ((symbolicRoots_actual_members known actualKnown concrete).mpr
    (List.mem_flatMap.mpr ⟨root, member, concreteMember⟩))


#print axioms Goose.GIR.RootsRefine.trans
#print axioms Goose.GIR.RootsRefine.expanded
#print axioms SymbolicRootsRefine.join
#print axioms SymbolicRootsRefine.actual
#print axioms SymbolicRootsRefine.contents
#print axioms SymbolicRootsRefine.rootMap

end ReplacementContentFlow.Model
end Goose.GIR
