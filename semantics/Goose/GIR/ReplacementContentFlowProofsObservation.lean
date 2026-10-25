import Goose.GIR.ReplacementContentFlowProofsCanonicalRoots

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem ownerTouches_subset (module : Module) (roots : List RootRef) :
    ownerTouches module roots ⊆ roots := by
  unfold ownerTouches
  split
  · intro root member
    exact (List.mem_filter.mp member).1
  · exact List.Subset.refl _

theorem ownerTouches_nonGlobal {module : Module} {roots : List RootRef} {root : RootRef}
    (external : ∀ global, root ≠ .global global) :
    root ∈ ownerTouches module roots ↔ root ∈ roots := by
  unfold ownerTouches
  split
  · cases root with
    | «local» slot => simp
    | param index => simp
    | global global => exact False.elim (external global rfl)
  · rfl

theorem ownerDependencies_pending (module : Module) (func : Func) :
    ownerDependencies module func .pending = none := rfl

theorem ownerDependencies_unknown (module : Module) (func : Func) :
    ownerDependencies module func .unknown = none := rfl

theorem ownerDependencies_local (module : Module) (func : Func) (slot : SlotId) :
    ownerDependencies module func (.known [.local slot]) = normalize func (.known [.local slot]) := rfl

theorem ownerDependencies_param (module : Module) (func : Func) (index : Nat) :
    ownerDependencies module func (.known [.param index]) = normalize func (.known [.param index]) := rfl

theorem ownerDependencies_contents (module : Module) (func : Func) (index : Nat) :
    ownerDependencies module func (.known [.contents index]) = normalize func (.known [.contents index]) := rfl

theorem ownerDependencies_literal_global (module : Module) (func : Func) (global : GlobalId) :
    ownerDependencies module func (.known [.global global]) = some (ownerTouches module [.global global]) := by
  unfold ownerDependencies rawOwnerTouches
  unfold ownerTouches
  split
  · cases retain : (module.globals[global]?).all (fun global => global.ty.ownerElem?.isSome) <;>
      simp [retain,Roots.bind,Roots.join,normalize,normalizeAtom,Atom.ofRootRef,unionRoots]
  · rfl

theorem normalize_singleton_atom {func : Func} {atom : Atom} {roots : List RootRef}
    (mapped : normalizeAtom func atom = some roots) :
    normalize func (.known [atom]) = some (unionRoots [] roots) := by
  simp [normalize,mapped]

theorem ownerDependencies_known {module : Module} {func : Func} {roots : Roots} {actual : List RootRef}
    (known : normalize func roots = some actual) :
    ∃ dependencies, ownerDependencies module func roots = some dependencies ∧ dependencies ⊆ actual := by
  obtain ⟨atoms,rfl⟩ := normalize_known_shape known
  apply normalize_bind_known
  intro atom member
  obtain ⟨mapped,mappedKnown,mappedWithin⟩ := (normalize_fold_atoms func atoms [] actual known).2 atom member
  cases atom with
  | «local» slot | param index | contents index =>
      all_goals refine ⟨unionRoots [] mapped,normalize_singleton_atom mappedKnown,?_⟩
      all_goals intro root present
      all_goals exact mappedWithin (((unionRoots_mem_iff _ _ _).mp present).resolve_left (by simp))
  | global global =>
      have actualMember : RootRef.global global ∈ actual :=
        (normalize_known_members known (.global global)).mpr ⟨.global global,member,[.global global],rfl,by simp⟩
      change ∃ dependencies, normalize func (.known ((ownerTouches module [.global global]).map Atom.ofRootRef)) =
        some dependencies ∧ dependencies ⊆ actual
      unfold ownerTouches
      split
      · cases retain : (module.globals[global]?).all (fun global => global.ty.ownerElem?.isSome) with
        | false => exact ⟨[],by simp [retain,normalize],by simp⟩
        | true =>
            refine ⟨[.global global],?_,?_⟩
            · simp [retain,normalize,normalizeAtom,Atom.ofRootRef,unionRoots]
            · intro root present
              have same : root = .global global := by simpa using present
              simpa [same] using actualMember
      · exact ⟨[.global global],rfl,by simpa using actualMember⟩

theorem callQuery_touch_dependencies {module : Module} {func : Func} {vt : Array (Option VTy)}
    {states : Array State} {state effects : State} {fn : FnId} {args : List ValueId}
    {roots : List RootRef}
    (called : callQuery module func vt states state fn args = some roots)
    (effectsAt : states[fn]? = some effects) :
    ∃ touched, ownerDependencies module func (substitute func state args (publicTouches effects.touched)) = some touched ∧
      touched ⊆ roots := by
  unfold callQuery at called
  dsimp only at called
  split at called
  · simp [failure,bind,Option.bind] at called
  · simp only [pure,bind,Option.bind,effectsAt] at called
    split at called
    · cases called
    · rename_i arguments argumentsAt
      dsimp only at called
      split at called
      · cases called
      · rename_i touched touchedAt
        cases called
        exact ⟨touched,touchedAt,fun root member => (unionRoots_mem_iff _ _ _).mpr (Or.inr member)⟩

#print axioms ownerDependencies_literal_global
#print axioms callQuery_touch_dependencies

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open ReplacementContentFlow.Model

theorem ReplacementFunctionFlow.ownerDependencies_of_value {flow : ReplacementFunctionFlow}
    {value : ValueId} {roots : List Goose.Core.RootRef} (known : flow.value value = some roots) :
    ∃ dependencies, flow.ownerDependencies value = some dependencies ∧ dependencies ⊆ roots := by
  rw [ReplacementFunctionFlow.value_model] at known
  rw [ReplacementFunctionFlow.ownerDependencies_model]
  cases built : flow.model with
  | none => simp [built] at known
  | some state =>
      simp only [built,Option.bind_some] at known ⊢
      exact ownerDependencies_known known

#print axioms ReplacementFunctionFlow.ownerDependencies_of_value

end Goose.GIR
