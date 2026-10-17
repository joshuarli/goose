import Goose.GIR.Validate
import Goose.Core.Sound.Frame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem unionRoots_contains_prior (left right : List RootRef) : left.Sublist (unionRoots left right) := by
  unfold unionRoots
  apply List.foldlRecOn (motive := fun roots => left.Sublist roots) right _ (List.Sublist.refl left)
  intro roots prior root member
  split
  · exact prior
  · exact prior.trans (List.sublist_append_left _ _)

theorem unionRoots_eq_prior_of_length {left right : List RootRef}
    (length : (unionRoots left right).length = left.length) : unionRoots left right = left :=
  ((unionRoots_contains_prior left right).eq_of_length_le (by omega)).symm

def ProvenanceExtends (before after : Prov) : Prop :=
  after.slots.size = before.slots.size ∧ after.vals.size = before.vals.size ∧
    (∀ cell root, root ∈ rootsAt before.slots cell → root ∈ rootsAt after.slots cell) ∧
    (∀ cell root, root ∈ rootsAt before.vals cell → root ∈ rootsAt after.vals cell)

theorem ProvenanceExtends.refl (provenance : Prov) : ProvenanceExtends provenance provenance :=
  ⟨rfl, rfl, fun _ _ present => present, fun _ _ present => present⟩

theorem ProvenanceExtends.trans {before middle after : Prov}
    (first : ProvenanceExtends before middle) (second : ProvenanceExtends middle after) :
    ProvenanceExtends before after :=
  ⟨second.1.trans first.1, second.2.1.trans first.2.1,
    fun cell root present => second.2.2.1 cell root (first.2.2.1 cell root present),
    fun cell root present => second.2.2.2 cell root (first.2.2.2 cell root present)⟩

theorem addTo_retains {table : Array (List RootRef)} {index cell : Nat}
    {roots : List RootRef} {root : RootRef} (present : root ∈ rootsAt table cell) :
    root ∈ rootsAt (addTo table index roots).1 cell := by
  unfold addTo
  dsimp only
  split
  · exact present
  · simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rename_i same
      subst cell
      split
      · exact Sound.unionRoots_left _ _ _ present
      · rename_i outside
        have absent : table[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
        simpa [rootsAt, absent] using present
    · exact present

theorem addTo_size (table : Array (List RootRef)) (index : Nat) (roots : List RootRef) :
    (addTo table index roots).1.size = table.size := by
  unfold addTo
  dsimp only
  split <;> simp

theorem addTo_inserts {table : Array (List RootRef)} {index : Nat}
    {roots : List RootRef} {root : RootRef} (bounded : index < table.size)
    (present : root ∈ roots) : root ∈ rootsAt (addTo table index roots).1 index := by
  unfold addTo
  dsimp only
  split
  · rename_i unchanged
    have length : (unionRoots (rootsAt table index) roots).length = (rootsAt table index).length := by
      simpa [Nat.not_le_of_gt bounded] using unchanged
    rw [← unionRoots_eq_prior_of_length length]
    exact Sound.unionRoots_right _ _ _ present
  · simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
      bounded, ite_true, Option.getD_some]
    exact Sound.unionRoots_right _ _ _ present

theorem ProvenanceExtends.addValues (provenance : Prov) (index : Nat) (roots : List RootRef) :
    ProvenanceExtends provenance { provenance with vals := (addTo provenance.vals index roots).1 } :=
  ⟨rfl, addTo_size _ _ _, fun _ _ present => present, fun _ _ present => addTo_retains present⟩

theorem ProvenanceExtends.addSlots (provenance : Prov) (index : Nat) (roots : List RootRef) :
    ProvenanceExtends provenance { provenance with slots := (addTo provenance.slots index roots).1 } :=
  ⟨addTo_size _ _ _, rfl, fun _ _ present => addTo_retains present, fun _ _ present => present⟩

private theorem edge_provenance_extends {func : Func} {original current : Prov}
    {changed : Bool} {target : BlockId} {args : List ValueId}
    (prior : ProvenanceExtends original current) :
    ProvenanceExtends original
      (match func.blocks[target]? with
      | none => (current, changed)
      | some block =>
        (block.params.zip args).foldl (fun (acc : Prov × Bool) (pair : (ValueId × VTy) × ValueId) =>
          let (p, changed) := acc
          let (param, argument) := pair
          let (values, inserted) := addTo p.vals param.1 (rootsAt p.vals argument)
          ({ p with vals := values }, changed || inserted)) (current, changed)).1 := by
  cases row : func.blocks[target]? with
  | none => exact prior
  | some block =>
    apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends original acc.1)
      (block.params.zip args) _ prior
    intro acc checked pair member
    exact checked.trans (ProvenanceExtends.addValues _ _ _)

theorem provRound_extends (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov) :
    ProvenanceExtends provenance (provRound results types func provenance).1 := by
  unfold provRound
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
    func.blocks.toList _ (ProvenanceExtends.refl provenance)
  intro acc checked block member
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
    block.insts _ checked
  intro step checked inst member
  cases inst with
  | «def» result op => exact checked.trans (ProvenanceExtends.addValues _ _ _)
  | eff effect =>
    cases effect with
    | slotInit slot value origin => exact checked.trans (ProvenanceExtends.addSlots _ _ _)
    | store address value origin =>
      apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
        (rootsAt step.1.vals address) _ checked
      intro acc checked root member
      cases root with
      | «local» slot => exact checked.trans (ProvenanceExtends.addSlots _ _ _)
      | _ => exact checked
    | _ => exact checked
  | term term =>
    cases term with
    | br target args => exact edge_provenance_extends checked
    | condbr condition left leftArgs right rightArgs =>
      exact edge_provenance_extends (edge_provenance_extends checked)
    | _ => exact checked

theorem provFix_extends (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (fuel : Nat) (provenance : Prov) :
    ProvenanceExtends provenance (provFix results types func fuel provenance) := by
  induction fuel generalizing provenance with
  | zero => exact .refl provenance
  | succ fuel ih =>
    change ProvenanceExtends provenance
      (if (provRound results types func provenance).2 then
        provFix results types func fuel (provRound results types func provenance).1
      else (provRound results types func provenance).1)
    split
    · exact (provRound_extends results types func provenance).trans (ih _)
    · exact provRound_extends results types func provenance

theorem list_foldl_establishes {property known : σ → Prop} (items : List α) (start : σ)
    (step : σ → α → σ) (target : α) (member : target ∈ items)
    (initial : property start)
    (preserved : ∀ state item, property state → property (step state item))
    (retained : ∀ state item, known state → known (step state item))
    (established : ∀ state, property state → known (step state target)) :
    known (items.foldl step start) := by
  induction items generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | later
    · subst first
      apply List.foldlRecOn (motive := known) rest step (established start initial)
      intro state checked item member
      exact retained state item checked
    · exact ih (step start first) later (preserved start first initial)

end Goose.Lower.Validation
