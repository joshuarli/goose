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

theorem provStep_extends (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov) (changed : Bool) (inst : Inst) :
    ProvenanceExtends provenance (func.provStep results types (provenance, changed) inst).1 := by
  unfold Func.provStep
  dsimp only
  cases inst with
  | «def» result op => exact ProvenanceExtends.addValues _ _ _
  | eff effect =>
    cases effect with
    | slotInit slot value origin => exact ProvenanceExtends.addSlots _ _ _
    | store address value origin =>
      apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
        (rootsAt provenance.vals address) _ (ProvenanceExtends.refl provenance)
      intro acc checked root member
      cases root with
      | «local» slot => exact checked.trans (ProvenanceExtends.addSlots _ _ _)
      | _ => exact checked
    | _ => exact .refl provenance
  | term term =>
    cases term with
    | br target args => exact edge_provenance_extends (.refl provenance)
    | condbr condition left leftArgs right rightArgs =>
      exact edge_provenance_extends (edge_provenance_extends (.refl provenance))
    | _ => exact .refl provenance

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
  exact checked.trans (provStep_extends results types func _ _ inst)

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

theorem provRound_static_definition (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {op : Op} (definition : .def result op ∈ block.insts)
    {root : RootRef} (produced : ∀ state, root ∈ rootsOfDef results types func state result op)
    (bounded : result < provenance.vals.size) :
    root ∈ rootsAt (provRound results types func provenance).1.vals result := by
  unfold provRound
  rw [← Array.foldl_toList]
  refine list_foldl_establishes
    (property := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
    (known := fun acc => root ∈ rootsAt acc.1.vals result)
    _ _ _ block blockMember (.refl provenance) ?_ ?_ ?_
  · intro state body checked
    apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
      body.insts _ checked
    intro acc checked inst member
    exact checked.trans (provStep_extends results types func _ _ inst)
  · intro state body known
    apply List.foldlRecOn (motive := fun acc : Prov × Bool => root ∈ rootsAt acc.1.vals result)
      body.insts _ known
    intro acc known inst member
    exact (provStep_extends results types func _ _ inst).2.2.2 result root known
  · intro state checked
    refine list_foldl_establishes
      (property := fun acc : Prov × Bool => ProvenanceExtends provenance acc.1)
      (known := fun acc => root ∈ rootsAt acc.1.vals result)
      _ _ _ (.def result op) definition checked ?_ ?_ ?_
    · intro acc inst checked
      exact checked.trans (provStep_extends results types func _ _ inst)
    · intro acc inst known
      exact (provStep_extends results types func _ _ inst).2.2.2 result root known
    · intro acc checked
      exact addTo_inserts (by rw [checked.2.1]; exact bounded) (produced acc.1)

theorem provStart_values_size (func : Func) (types : Array (Option VTy)) :
    (provStart types func).vals.size = func.numValues := by
  unfold provStart
  cases row : func.blocks[0]? with
  | none => simp
  | some block =>
    apply List.foldlRecOn (motive := fun vals : Array (List RootRef) => vals.size = func.numValues)
      block.params.zipIdx _ (by simp)
    intro vals size pair member
    dsimp only
    split <;> simpa using size

theorem provenance_static_definition (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {op : Op} (definition : .def result op ∈ block.insts)
    {root : RootRef} (produced : ∀ state, root ∈ rootsOfDef results types func state result op)
    (bounded : result < func.numValues) :
    root ∈ rootsAt (func.provenance results types rootCount).vals result := by
  have known := provRound_static_definition results types func (provStart types func)
    blockMember definition produced (by simpa only [provStart_values_size] using bounded)
  unfold Func.provenance
  generalize fuelEq : (func.numValues + func.slots.size + 1) * (rootCount + 1) = fuel
  cases fuel with
  | zero =>
    have positive : 0 < (func.numValues + func.slots.size + 1) * (rootCount + 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  | succ fuel =>
    change root ∈ rootsAt
      (if (provRound results types func (provStart types func)).2 then
        provFix results types func fuel (provRound results types func (provStart types func)).1
      else (provRound results types func (provStart types func)).1).vals result
    split
    · exact (provFix_extends results types func fuel _).2.2.2 result root known
    · exact known

theorem provenance_slotAddr (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {slot : SlotId} (definition : .def result (.slotAddr slot) ∈ block.insts)
    (bounded : result < func.numValues) :
    RootRef.local slot ∈ rootsAt (func.provenance results types rootCount).vals result :=
  provenance_static_definition results types func rootCount blockMember definition
    (fun _ => by simp [rootsOfDef]) bounded

theorem provenance_globalAddr (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {global : GlobalId} (definition : .def result (.globalAddr global) ∈ block.insts)
    (bounded : result < func.numValues) :
    RootRef.global global ∈ rootsAt (func.provenance results types rootCount).vals result :=
  provenance_static_definition results types func rootCount blockMember definition
    (fun _ => by simp [rootsOfDef]) bounded

theorem replacementQueries_values (module : GIR.Module) (func : Func) (types : Array (Option VTy)) (provenance : Prov) (value : ValueId) :
    ((replacementQueries module func types provenance).value value).getD [] =
      (rootsAt provenance.vals value).flatMap func.expandParameterRoot := by
  cases roots : rootsAt provenance.vals value with
  | nil =>
    by_cases empty : (replacementEmptyValues module func types provenance)[value]?.getD false = true
    all_goals simp [ReplacementQueries.value, replacementQueries, roots, empty]
  | cons root rest =>
    simp only [ReplacementQueries.value, replacementQueries, roots, Option.getD_some]
    rfl

theorem replacementQueries_known_empty (module : GIR.Module) (func : Func) (types : Array (Option VTy)) (provenance : Prov) (value : ValueId)
    (present : rootsAt provenance.vals value ≠ [])
    (empty : ∀ root ∈ rootsAt provenance.vals value, func.expandParameterRoot root = []) :
    (replacementQueries module func types provenance).value value = some [] := by
  have normalized := List.flatMap_eq_nil_iff.mpr empty
  cases roots : rootsAt provenance.vals value with
  | nil => exact False.elim (present roots)
  | cons root rest =>
    simp only [ReplacementQueries.value, replacementQueries, roots]
    change some ((root :: rest).flatMap (replacementQueries module func types provenance).expand) = some []
    change some ((root :: rest).flatMap func.expandParameterRoot) = some []
    exact congrArg some (roots ▸ normalized)

theorem replacementQueries_unknown (module : GIR.Module) (func : Func) (types : Array (Option VTy)) (provenance : Prov) (value : ValueId)
    (unknown : rootsAt provenance.vals value = [])
    (notEmpty : (replacementEmptyValues module func types provenance)[value]?.getD false = false) :
    (replacementQueries module func types provenance).value value = none := by
  simp [ReplacementQueries.value, replacementQueries, unknown, notEmpty]

theorem replacementQueries_slotAddr (module : GIR.Module) (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {slot : SlotId} (definition : .def result (.slotAddr slot) ∈ block.insts)
    (bounded : result < func.numValues) :
    RootRef.local slot ∈ ((replacementQueries module func types (func.provenance results types rootCount)).value result).getD [] := by
  rw [replacementQueries_values]
  exact List.mem_flatMap.mpr ⟨.local slot,
    provenance_slotAddr results types func rootCount blockMember definition bounded,
    by simp [Func.expandParameterRoot]⟩

theorem replacementQueries_globalAddr (module : GIR.Module) (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {global : GlobalId} (definition : .def result (.globalAddr global) ∈ block.insts)
    (bounded : result < func.numValues) :
    RootRef.global global ∈ ((replacementQueries module func types (func.provenance results types rootCount)).value result).getD [] := by
  rw [replacementQueries_values]
  exact List.mem_flatMap.mpr ⟨.global global,
    provenance_globalAddr results types func rootCount blockMember definition bounded,
    by simp [Func.expandParameterRoot]⟩

end Goose.Lower.Validation
