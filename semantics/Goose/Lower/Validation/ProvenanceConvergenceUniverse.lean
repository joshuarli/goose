import Goose.Lower.Validation.ProvenanceConvergenceGrowth

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.Core.Sound Goose.GIR

def AddressBound (rootUniverse : List RootRef) : Op → Prop
  | .slotAddr slot => RootRef.local slot ∈ rootUniverse
  | .globalAddr global => RootRef.global global ∈ rootUniverse
  | _ => True

structure RootUniverse (results : Array (List RootRef)) (func : Func) (roots : List RootRef) : Prop where
  entry : ∀ block, func.blocks[0]? = some block → ∀ param ∈ block.params.zipIdx,
    RootRef.param param.2 ∈ roots
  addresses : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts → AddressBound roots op
  contents : ∀ row ∈ func.roots.contents, row.2 ⊆ roots
  slotSeeds : ∀ row ∈ func.roots.slots.getD #[], row.2 ⊆ roots
  results : ∀ callee global, RootRef.global global ∈ rootsAt results callee → RootRef.global global ∈ roots

private theorem annotation_subset {func : Func} {roots : List RootRef}
    (bound : ∀ row ∈ func.roots.contents, row.2 ⊆ roots) (index : Nat) :
    ((func.roots.contents.find? (·.1 == index)).map (·.2)).getD [] ⊆ roots := by
  cases found : func.roots.contents.find? (·.1 == index) with
  | none => simp
  | some row =>
    simp only [Option.map_some, Option.getD_some]
    exact bound row (Array.mem_of_find?_eq_some found)

theorem rootsOfDef_subset {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    {provenance : Prov} (bound : Bounded roots provenance) (value : ValueId) (op : Op)
    (address : AddressBound roots op) : rootsOfDef results types func provenance value op ⊆ roots := by
  intro root member
  cases op <;> simp only [rootsOfDef] at member
  all_goals try { simp at member }
  all_goals try { exact (bound.2 _).2 member }
  case slotAddr slot =>
    have equal : root = RootRef.local slot := by simpa only [List.mem_singleton] using member
    subst root
    exact address
  case globalAddr global =>
    have equal : root = RootRef.global global := by simpa only [List.mem_singleton] using member
    subst root
    exact address
  case load owner =>
    split at member
    · rcases unionRoots_mem _ _ _ member with stored | contents
      · obtain ⟨ownerRoot, _, stored⟩ := List.mem_flatMap.mp stored
        cases ownerRoot with
        | «local» slot => exact (bound.1 slot).2 stored
        | _ => simp at stored
      · split at contents
        · obtain ⟨ownerRoot, _, contents⟩ := List.mem_flatMap.mp contents
          cases ownerRoot with
          | param index =>
            simp only at contents
            split at contents
            · split at contents
              · exact annotation_subset universeBound.contents index contents
              · simp at contents
            · simp at contents
          | _ => simp at contents
        · simp at contents
    · simp at member
  case call callee args origin =>
    obtain ⟨calleeRoot, calleeMember, member⟩ := List.mem_flatMap.mp member
    cases calleeRoot with
    | param index =>
      cases arg : args[index]? with
      | none => simp [arg] at member
      | some argument => exact (bound.2 argument).2 (by simpa only [arg] using member)
    | «global» global =>
      have equal : root = RootRef.global global := by simpa only [List.mem_singleton] using member
      subst root
      exact universeBound.results callee global calleeMember
    | «local» slot => simp at member

private theorem edge_bounded {func : Func} {roots : List RootRef} {state : Prov × Bool}
    (bound : Bounded roots state.1) (target : BlockId) (args : List ValueId) :
    Bounded roots
      (match func.blocks[target]? with
      | none => state
      | some block =>
        (block.params.zip args).foldl (fun (acc : Prov × Bool) (pair : (ValueId × VTy) × ValueId) =>
          let (p, changed) := acc
          let (param, argument) := pair
          let (values, inserted) := GIR.addTo p.vals param.1 (rootsAt p.vals argument)
          ({ p with vals := values }, changed || inserted)) state).1 := by
  cases row : func.blocks[target]? with
  | none => exact bound
  | some block =>
    apply List.foldlRecOn (motive := fun acc : Prov × Bool => Bounded roots acc.1) _ _ bound
    intro acc prior pair _
    exact ⟨prior.1, prior.2.addTo _ (prior.2 pair.2).2⟩

theorem provStep_bounded {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    {state : Prov × Bool} (bound : Bounded roots state.1) (inst : Inst)
    (address : ∀ value op, inst = .def value op → AddressBound roots op) :
    Bounded roots (func.provStep results types state inst).1 := by
  cases inst with
  | «def» value op =>
    exact ⟨bound.1, bound.2.addTo value (rootsOfDef_subset universeBound bound value op (address _ _ rfl))⟩
  | eff effect =>
    cases effect with
    | slotInit slot value origin => exact ⟨bound.1.addTo slot (bound.2 value).2, bound.2⟩
    | store owner value origin =>
      apply List.foldlRecOn (motive := fun acc : Prov × Bool => Bounded roots acc.1) _ _ bound
      intro acc prior root _
      cases root with
      | «local» slot => exact ⟨prior.1.addTo slot (prior.2 value).2, prior.2⟩
      | _ => exact prior
    | _ => exact bound
  | term term =>
    cases term with
    | br target args => exact edge_bounded bound target args
    | condbr condition left leftArgs right rightArgs =>
      exact edge_bounded (edge_bounded bound left leftArgs) right rightArgs
    | _ => exact bound

theorem provRound_bounded {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    {provenance : Prov} (bound : Bounded roots provenance) :
    Bounded roots (provRound results types func provenance).1 := by
  unfold provRound
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => Bounded roots acc.1) _ _ bound
  intro acc prior block blockMember
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => Bounded roots acc.1) _ _ prior
  intro state prior inst instMember
  apply provStep_bounded universeBound prior inst
  intro value op equal
  exact universeBound.addresses block blockMember value op (equal ▸ instMember)

theorem TableBound.empty (roots : List RootRef) (count : Nat) :
    TableBound roots (Array.replicate count []) := by
  intro cell
  simp only [rootsAt, Array.getElem?_replicate]
  split <;> simp

theorem provStart_bounded {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots) :
    Bounded roots (provStart types func) := by
  constructor
  · intro slot
    simp only [provStart, Func.slotRootSeeds, rootsAt, Array.getElem?_mapIdx]
    cases row : func.slots[slot]? with
    | none => simp [row]
    | some descriptor =>
      simp only [row, Option.map_some, Option.getD_some]
      rw [← Array.foldl_toList]
      apply List.foldlRecOn (motive := fun values => values.Nodup ∧ values ⊆ roots) _ _ ⟨by simp, by simp⟩
      intro values prior annotation member
      by_cases same : annotation.1 == slot
      · rw [if_pos same]
        exact ⟨unionRoots_nodup prior.1,
          unionRoots_subset prior.2 (universeBound.slotSeeds annotation (Array.mem_toList_iff.mp member))⟩
      · simpa only [same, Bool.false_eq_true, ite_false] using prior
  · unfold provStart
    cases entry : func.blocks[0]? with
    | none => exact TableBound.empty _ _
    | some block =>
      apply List.foldlRecOn (motive := TableBound roots) block.params.zipIdx _ (TableBound.empty _ _)
      intro table prior param member
      dsimp only
      split
      · apply prior.set _ (by simp)
        intro root atRoot
        have equal : root = RootRef.param param.2 := by simpa only [List.mem_singleton] using atRoot
        subst root
        exact universeBound.entry block entry param member
      · exact prior

end Goose.Lower.Validation.ProvenanceConvergence
