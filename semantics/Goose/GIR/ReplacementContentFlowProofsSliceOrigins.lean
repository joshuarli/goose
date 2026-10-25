import Goose.GIR.ReplacementContentFlowProofsObservation
import Goose.GIR.ReplacementContentFlowProofsSliceTyping
import Goose.GIR.ReplacementContentFlowProofsCanonicalReachable
import Goose.GIR.ReplacementContentFlowProofsSteps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private def strictMerge (left right : Roots) : Roots :=
  match left, right with
  | .unknown, _ | _, .unknown => .unknown
  | .pending, _ | _, .pending => .pending
  | left, right => left.join right

private theorem strictFold_unknown (atoms : List Atom) (map : Atom → Roots) :
    atoms.foldl (fun acc atom => strictMerge acc (map atom)) .unknown = .unknown := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simpa [strictMerge] using ih

private theorem strictFold_pending (atoms : List Atom) (map : Atom → Roots) :
    ∀ output, atoms.foldl (fun acc atom => strictMerge acc (map atom)) .pending ≠ .known output := by
  induction atoms with
  | nil => intro output; simp
  | cons atom rest ih =>
      intro output
      cases equation : map atom with
      | pending => simpa [strictMerge,equation] using ih output
      | known roots => simpa [strictMerge,equation] using ih output
      | unknown =>
          simp only [List.foldl_cons,equation,strictMerge] at *
          have gone := strictFold_unknown rest map
          change rest.foldl (fun acc atom => strictMerge acc (map atom)) Roots.unknown = Roots.unknown at gone
          change rest.foldl (fun acc atom => strictMerge acc (map atom)) Roots.unknown ≠ Roots.known output
          rw [gone]
          simp

theorem Roots.join_known_members (left right : List Atom) (atom : Atom) :
    ∃ output, (Roots.known left).join (.known right) = .known output ∧
      (atom ∈ output ↔ atom ∈ left ∨ atom ∈ right) := by
  refine ⟨_,rfl,?_⟩
  change atom ∈ right.foldl (fun roots root => if roots.contains root then roots else roots ++ [root]) left ↔ _
  induction right generalizing left with
  | nil => simp
  | cons head rest ih =>
      simp only [List.foldl_cons,ih,List.mem_cons]
      by_cases present : head ∈ left
      · have yes : left.contains head = true := List.contains_iff_mem.mpr present
        simp only [yes,ite_true]
        constructor
        · intro member; exact member.elim Or.inl (fun h => Or.inr (Or.inr h))
        · intro member
          rcases member with member | equal | member
          · exact Or.inl member
          · subst atom; exact Or.inl present
          · exact Or.inr member
      · have no : left.contains head = false := by simpa using present
        simp only [no,Bool.false_eq_true,ite_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        exact or_assoc

private theorem strictFold_known (atoms : List Atom) (map : Atom → Roots) (initial output : List Atom)
    (known : atoms.foldl (fun acc atom => strictMerge acc (map atom)) (.known initial) = .known output) :
    initial ⊆ output ∧ ∀ atom ∈ atoms, ∃ mapped, map atom = .known mapped ∧ mapped ⊆ output := by
  induction atoms generalizing initial with
  | nil => cases known; exact ⟨List.Subset.refl _,by simp⟩
  | cons atom rest ih =>
      cases equation : map atom with
      | pending => exact False.elim (strictFold_pending rest map output (by simpa [strictMerge,equation] using known))
      | unknown =>
          have gone := strictFold_unknown rest map
          have contradiction : Roots.unknown = .known output := gone.symm.trans (by simpa only [List.foldl_cons,equation,strictMerge] using known)
          cases contradiction
      | known mapped =>
          obtain ⟨joined,joinedAt,_⟩ := Roots.join_known_members initial mapped atom
          have later : rest.foldl (fun acc atom => strictMerge acc (map atom)) (.known joined) = .known output := by
            simpa [strictMerge,equation,joinedAt] using known
          obtain ⟨joinedWithin,maps⟩ := ih joined later
          have initialWithin : initial ⊆ joined := by
            intro root member
            obtain ⟨other,otherAt,members⟩ := Roots.join_known_members initial mapped root
            have same : other = joined := Roots.known.inj (otherAt.symm.trans joinedAt)
            exact same ▸ (members.mpr (Or.inl member))
          have mappedWithin : mapped ⊆ joined := by
            intro root member
            obtain ⟨other,otherAt,members⟩ := Roots.join_known_members initial mapped root
            have same : other = joined := Roots.known.inj (otherAt.symm.trans joinedAt)
            exact same ▸ (members.mpr (Or.inr member))
          refine ⟨fun _ member => joinedWithin (initialWithin member),?_⟩
          intro root member
          rcases List.mem_cons.mp member with equal | member
          · subst root
            exact ⟨mapped,equation,fun _ member => joinedWithin (mappedWithin member)⟩
          · exact maps root member

theorem Roots.bind_known_maps {atoms output : List Atom} {map : Atom → Roots}
    (known : (Roots.known atoms).bind map = .known output) :
    ∀ atom ∈ atoms, ∃ mapped, map atom = .known mapped ∧ mapped ⊆ output :=
  (strictFold_known atoms map [] output known).2

theorem normalize_known_subset {func : Func} {before after : List Atom} {actual : List RootRef}
    (within : before ⊆ after) (known : normalize func (.known after) = some actual) :
    ∃ roots, normalize func (.known before) = some roots ∧ roots ⊆ actual := by
  apply normalize_fold_within func before actual
  · intro atom member
    exact (normalize_fold_atoms func after [] actual known).2 atom (within member)
  · simp

theorem ownerDependencies_known_subset {module : Module} {func : Func}
    {before after : List Atom} {actual : List RootRef}
    (within : before ⊆ after) (known : ownerDependencies module func (.known after) = some actual) :
    ∃ roots, ownerDependencies module func (.known before) = some roots ∧ roots ⊆ actual := by
  obtain ⟨projected,projectedAt⟩ := normalize_known_shape known
  have mapped := Roots.bind_known_maps projectedAt
  apply normalize_bind_known
  intro atom member
  obtain ⟨roots,rootsAt,included⟩ := mapped atom (within member)
  rw [rootsAt]
  exact normalize_known_subset included (by simpa only [ownerDependencies,projectedAt] using known)

theorem ownerDependencies_of_extends {module : Module} {func : Func} {before after : Roots}
    {actual : List RootRef} (growth : before.Extends after)
    (ready : before ≠ .pending) (known : ownerDependencies module func after = some actual) :
    ∃ roots, ownerDependencies module func before = some roots ∧ roots ⊆ actual := by
  cases before with
  | pending => exact False.elim (ready rfl)
  | unknown =>
      cases after <;> simp_all [Roots.Extends,ownerDependencies,rawOwnerTouches,Roots.bind,normalize]
  | known before =>
      cases after with
      | pending => exact False.elim growth
      | unknown => simp [ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
      | known after => exact ownerDependencies_known_subset growth.subset known

theorem ownerDependencies_join_right {module : Module} {func : Func} {left right : Roots}
    {actual : List RootRef} (ready : right ≠ .pending)
    (known : ownerDependencies module func (left.join right) = some actual) :
    ∃ roots, ownerDependencies module func right = some roots ∧ roots ⊆ actual := by
  cases left with
  | pending =>
      refine ⟨actual,?_,List.Subset.refl _⟩
      cases right <;> simpa [Roots.join] using known
  | unknown => simp [Roots.join,ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
  | known left =>
      cases right with
      | pending => exact False.elim (ready rfl)
      | unknown => simp [Roots.join,ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
      | known right =>
          obtain ⟨joined,joinedAt,_⟩ := Roots.join_known_members left right (.global 0)
          apply ownerDependencies_known_subset (after := joined) ?_ (by rwa [joinedAt] at known)
          intro root member
          obtain ⟨other,otherAt,members⟩ := Roots.join_known_members left right root
          have same : other = joined := Roots.known.inj (otherAt.symm.trans joinedAt)
          exact same ▸ members.mpr (Or.inr member)

theorem touchValues_source_dependencies {module : Module} {func : Func} {vt : Array (Option VTy)}
    {state : State} {values : List ValueId} {source : ValueId} {actual : List RootRef}
    (member : source ∈ values) (reference : valRefLike vt source = true)
    (ready : flowAt state.values source ≠ .pending)
    (known : ownerDependencies module func (touchValues vt state values).touched = some actual) :
    ∃ roots, ownerDependencies module func (flowAt state.values source) = some roots ∧ roots ⊆ actual := by
  induction values generalizing state with
  | nil => simp at member
  | cons head rest ih =>
      let next := touchValues vt state [head]
      have restKnown : ownerDependencies module func (touchValues vt next rest).touched = some actual := known
      rcases List.mem_cons.mp member with equal | member
      · subst head
        have exposed : next.touched = state.touched.join (flowAt state.values source) := by
          simp [next,touchValues,reference]
        have growth := (touchValues_extends vt next rest).touched
        obtain ⟨joined,joinedKnown,joinedWithin⟩ := ownerDependencies_of_extends growth
          (by rw [exposed]; exact Roots.join_ready_right _ _ ready) restKnown
        rw [exposed] at joinedKnown
        obtain ⟨roots,rootsKnown,rootsWithin⟩ := ownerDependencies_join_right ready joinedKnown
        exact ⟨roots,rootsKnown,fun _ member => joinedWithin (rootsWithin member)⟩
      · exact ih (state := next) member ready restKnown

theorem step_access_extends (module : Module) (states : Array State) (func : Func)
    (vt : Array (Option VTy)) (state : State) (inst : Inst)
    (ordinary : ∀ value fn args origin, inst ≠ .def value (.call fn args origin)) :
    (touchValues vt state (accessOperands inst)).Extends (step module states func vt state inst) := by
  cases inst with
  | «def» value op =>
      cases op <;> simp only [step,Id.run_pure]
      case call fn args origin => exact False.elim (ordinary _ _ _ _ rfl)
      all_goals exact (State.extends_values _ _ _).trans (touchValues_extends _ _ _)
  | eff effect =>
      cases effect <;> simp only [step,Id.run_pure]
      case slotInit slot value origin => exact State.extends_slots _ _ _
      case store address value origin =>
        split
        · exact write_extends _ _ _ _
        · exact State.Extends.refl _
      all_goals exact State.Extends.refl _
  | term term =>
      cases term <;> simp only [step,Id.run_pure]
      case br target args => exact edge_extends _ _ _ _
      case condbr condition left leftArgs right rightArgs =>
        exact (edge_extends _ _ _ _).trans (edge_extends _ _ _ _)
      case ret values origin =>
        cases values with
        | nil => exact State.Extends.refl _
        | cons value rest =>
            cases rest with
            | nil => exact State.extends_returned _ _
            | cons next rest => exact State.Extends.refl _
      all_goals exact State.Extends.refl _

theorem fixed_step_access_dependencies {module : Module} {states : Array State} {func : Func}
    {vt : Array (Option VTy)} {state : State} {inst : Inst} {source : ValueId} {actual : List RootRef}
    (fixed : step module states func vt state inst = state)
    (ordinary : ∀ value fn args origin, inst ≠ .def value (.call fn args origin))
    (member : source ∈ accessOperands inst) (reference : valRefLike vt source = true)
    (ready : flowAt state.values source ≠ .pending)
    (known : ownerDependencies module func state.touched = some actual) :
    ∃ roots, ownerDependencies module func (flowAt state.values source) = some roots ∧ roots ⊆ actual := by
  have initialReady : state.touched ≠ .pending := by
    intro same
    simp [same,ownerDependencies,rawOwnerTouches,Roots.bind,normalize] at known
  have growth := step_access_extends module states func vt state inst ordinary
  rw [fixed] at growth
  obtain ⟨exposed,exposedKnown,exposedWithin⟩ := ownerDependencies_of_extends growth.touched
    ((touchValues_extends vt state (accessOperands inst)).touched.ready initialReady) known
  obtain ⟨roots,rootsKnown,rootsWithin⟩ := touchValues_source_dependencies member reference ready exposedKnown
  exact ⟨roots,rootsKnown,fun _ member => exposedWithin (rootsWithin member)⟩

theorem fixed_slice_load_dependencies {module : Module} {states : Array State} {func : Func}
    {vt : Array (Option VTy)} {state : State} {value address : ValueId}
    {mutability : Mutability} {element : Ty} {actual : List RootRef}
    (fixed : step module states func vt state (.def value (.load address)) = state)
    (typed : vt[value]? = some (some (.data (.slice mutability element))))
    (ready : flowAt state.values value ≠ .pending)
    (known : ownerDependencies module func state.touched = some actual) :
    ∃ roots, ownerDependencies module func (flowAt state.values value) = some roots ∧ roots ⊆ actual := by
  let before := touchValues vt state (accessOperands (.def value (.load address)))
  let after := { before with values := addFlow before.values value (result func vt before value (.load address)) }
  have fixedAfter : touchValues vt after [value] = state := by
    simpa [after,before,step,interiorLoadedResults,loadedResults,typed,Ty.isRefLike,Ty.interiorTarget?] using fixed
  have outputKnown : ownerDependencies module func (touchValues vt after [value]).touched = some actual := by
    rw [fixedAfter]
    exact known
  have outputValues : after.values = state.values := by
    have same := congrArg State.values fixedAfter
    exact same
  have reference : valRefLike vt value = true := by simp [valRefLike,typed,VTy.refLike,Ty.isRefLike]
  simpa only [outputValues] using touchValues_source_dependencies (module := module) (func := func)
    (state := after) (by simp : value ∈ [value]) reference (by simpa only [outputValues] using ready) outputKnown

theorem Roots.AtomsWithin.bind_atom {atoms output : List Atom} {map : Atom → Roots}
    {predicate : Atom → Prop} (known : (Roots.known atoms).bind map = .known output)
    (bounded : (Roots.known output).AtomsWithin predicate) {atom : Atom} (member : atom ∈ atoms) :
    (map atom).AtomsWithin predicate := by
  obtain ⟨mapped,mappedAt,mappedWithin⟩ := Roots.bind_known_maps known atom member
  rw [mappedAt]
  exact fun root present => bounded root (mappedWithin present)

theorem content_atomsWithin_of_extends {func : Func} {before after : State}
    {beforeAddress afterAddress : Roots} {predicate : Atom → Prop}
    (growth : before.Extends after) (addresses : beforeAddress.Extends afterAddress)
    (bounded : (content func after afterAddress).AtomsWithin predicate)
    (ready : content func after afterAddress ≠ .pending) :
    (content func before beforeAddress).AtomsWithin predicate := by
  cases afterAddress with
  | pending => exact False.elim (ready rfl)
  | unknown => exact False.elim bounded
  | known afterAtoms =>
      cases outputAt : content func after (.known afterAtoms) with
      | pending => exact False.elim (ready outputAt)
      | unknown => rw [outputAt] at bounded; exact False.elim bounded
      | known output =>
          cases beforeAddress with
          | pending => trivial
          | unknown => exact False.elim addresses
          | known beforeAtoms =>
              apply Roots.AtomsWithin.bind_known
              intro atom member
              have mapped := Roots.AtomsWithin.bind_atom outputAt (by simpa only [outputAt] using bounded)
                (addresses.subset member)
              cases atom with
              | «local» slot => exact (growth.slots.values slot).atomsWithin mapped
              | param index =>
                  dsimp only at mapped ⊢
                  split at mapped
                  · rename_i reference
                    rw [if_pos reference]
                    exact (growth.contents.values index).atomsWithin mapped
                  · exact False.elim mapped
              | global global | contents index => exact False.elim mapped

theorem Roots.AtomsWithin.join_left {predicate : Atom → Prop} {left right : Roots}
    (bounded : (left.join right).AtomsWithin predicate) : left.AtomsWithin predicate := by
  cases left with
  | pending => trivial
  | unknown => exact False.elim bounded
  | known left =>
      cases right with
      | pending => exact bounded
      | unknown => exact False.elim bounded
      | known right =>
          intro atom member
          obtain ⟨joined,joinedAt,members⟩ := Roots.join_known_members left right atom
          rw [joinedAt] at bounded
          exact bounded atom (members.mpr (Or.inl member))

theorem Roots.AtomsWithin.join_right {predicate : Atom → Prop} {left right : Roots}
    (bounded : (left.join right).AtomsWithin predicate) : right.AtomsWithin predicate := by
  cases right with
  | pending => trivial
  | unknown => cases left <;> exact False.elim bounded
  | known right =>
      cases left with
      | pending => exact bounded
      | unknown => exact False.elim bounded
      | known left =>
          intro atom member
          obtain ⟨joined,joinedAt,members⟩ := Roots.join_known_members left right atom
          rw [joinedAt] at bounded
          exact bounded atom (members.mpr (Or.inr member))

theorem touchValues_source_atomsWithin {vt : Array (Option VTy)} {state : State}
    {values : List ValueId} {source : ValueId} {predicate : Atom → Prop}
    (member : source ∈ values) (reference : valRefLike vt source = true)
    (bounded : (touchValues vt state values).touched.AtomsWithin predicate) :
    (flowAt state.values source).AtomsWithin predicate := by
  induction values generalizing state with
  | nil => simp at member
  | cons head rest ih =>
      let next := touchValues vt state [head]
      have restBound : (touchValues vt next rest).touched.AtomsWithin predicate := bounded
      rcases List.mem_cons.mp member with equal | member
      · subst head
        have exposed : next.touched = state.touched.join (flowAt state.values source) := by
          simp [next,touchValues,reference]
        have beforeBound := (touchValues_extends vt next rest).touched.atomsWithin restBound
        rw [exposed] at beforeBound
        exact beforeBound.join_right
      · exact ih (state := next) member restBound

theorem fixed_step_access_atomsWithin {module : Module} {states : Array State} {func : Func}
    {vt : Array (Option VTy)} {state : State} {inst : Inst} {source : ValueId} {predicate : Atom → Prop}
    (fixed : step module states func vt state inst = state)
    (ordinary : ∀ value fn args origin, inst ≠ .def value (.call fn args origin))
    (member : source ∈ accessOperands inst) (reference : valRefLike vt source = true)
    (bounded : state.touched.AtomsWithin predicate) :
    (flowAt state.values source).AtomsWithin predicate := by
  have growth := step_access_extends module states func vt state inst ordinary
  rw [fixed] at growth
  exact touchValues_source_atomsWithin member reference (growth.touched.atomsWithin bounded)

theorem Roots.bind_all_known (atoms : List Atom) (map : Atom → Roots)
    (mapped : ∀ atom ∈ atoms, ∃ roots, map atom = .known roots) :
    ∃ output, (Roots.known atoms).bind map = .known output := by
  suffices ∀ initial : List Atom, ∃ output,
      atoms.foldl (fun acc atom => strictMerge acc (map atom)) (.known initial) = .known output from this []
  intro initial
  induction atoms generalizing initial with
  | nil => exact ⟨initial,rfl⟩
  | cons atom rest ih =>
      obtain ⟨roots,rootsAt⟩ := mapped atom (by simp)
      obtain ⟨joined,joinedAt,_⟩ := Roots.join_known_members initial roots atom
      obtain ⟨output,outputAt⟩ := ih (fun atom member => mapped atom (List.mem_cons_of_mem _ member)) joined
      exact ⟨output,by simpa only [List.foldl_cons,rootsAt,strictMerge,joinedAt] using outputAt⟩

#print axioms Roots.join_known_members
#print axioms Roots.bind_known_maps

end Goose.GIR.ReplacementContentFlow.Model
