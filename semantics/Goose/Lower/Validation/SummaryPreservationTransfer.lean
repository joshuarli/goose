import Goose.Lower.Validation.SummaryPreservationProvenance

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def EdgeRootsClosed (func : Func) (upper : Prov) (target : BlockId)
    (args : List ValueId) : Prop :=
  ∀ block, func.blocks[target]? = some block →
    ∀ pair ∈ block.params.zip args,
      ∀ root ∈ rootsAt upper.vals pair.2, root ∈ rootsAt upper.vals pair.1.1

def InstructionRootsClosed (res : Array (List RootRef)) (vt : Array (Option VTy))
    (func : Func) (upper : Prov) : Inst → Prop
  | .def result op => ∀ root ∈ rootsOfDef res vt func upper result op,
      root ∈ rootsAt upper.vals result
  | .eff (.slotInit slot value _) => ∀ root ∈ rootsAt upper.vals value,
      root ∈ rootsAt upper.slots slot
  | .eff (.store address value _) => ∀ slot, RootRef.local slot ∈ rootsAt upper.vals address →
      ∀ root ∈ rootsAt upper.vals value, root ∈ rootsAt upper.slots slot
  | .term (.br target args) => EdgeRootsClosed func upper target args
  | .term (.condbr _ left leftArgs right rightArgs) =>
      EdgeRootsClosed func upper left leftArgs ∧ EdgeRootsClosed func upper right rightArgs
  | _ => True

private theorem edge_below {func : Func} {upper current : Prov} {changed : Bool}
    {target : BlockId} {args : List ValueId} (prior : ProvenanceBelow current upper)
    (closed : EdgeRootsClosed func upper target args) :
    ProvenanceBelow
      (match func.blocks[target]? with
      | none => (current, changed)
      | some block =>
        (block.params.zip args).foldl (fun (acc : Prov × Bool) (pair : (ValueId × VTy) × ValueId) =>
          let (p, changed) := acc
          let (param, argument) := pair
          let (values, inserted) := addTo p.vals param.1 (rootsAt p.vals argument)
          ({ p with vals := values }, changed || inserted)) (current, changed)).1 upper := by
  cases lookup : func.blocks[target]? with
  | none => exact prior
  | some block =>
    apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceBelow acc.1 upper)
      (block.params.zip args) _ prior
    intro acc bounded pair member
    exact ⟨bounded.slots, addTo_below bounded.vals (fun root rootMember =>
      closed block lookup pair member root (bounded.vals _ _ rootMember))⟩

theorem provRound_below {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper current : Prov}
    (closed : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionRootsClosed res vt func upper inst)
    (prior : ProvenanceBelow current upper) :
    ProvenanceBelow (provRound res vt func current).1 upper := by
  unfold provRound
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceBelow acc.1 upper)
    func.blocks.toList _ prior
  intro acc bounded block blockMember
  apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceBelow acc.1 upper)
    block.insts _ bounded
  intro step bounded inst instMember
  have instruction := closed block blockMember inst instMember
  cases inst with
  | «def» result op =>
    exact ⟨bounded.slots, addTo_below bounded.vals (fun root rootMember =>
      instruction root (rootsOfDef_mono (fun _ _ member => member) bounded op root rootMember))⟩
  | eff effect =>
    cases effect with
    | slotInit slot value origin =>
      exact ⟨addTo_below bounded.slots (fun root rootMember =>
        instruction root (bounded.vals _ _ rootMember)), bounded.vals⟩
    | store address value origin =>
      have original := bounded
      apply List.foldlRecOn (motive := fun acc : Prov × Bool => ProvenanceBelow acc.1 upper)
        (rootsAt step.1.vals address) _ bounded
      intro acc bounded root rootMember
      cases root with
      | «local» slot =>
        exact ⟨addTo_below bounded.slots (fun root member =>
          instruction slot (original.vals _ _ rootMember) root (bounded.vals _ _ member)), bounded.vals⟩
      | _ => exact bounded
    | _ => exact bounded
  | term term =>
    cases term with
    | br target args => exact edge_below bounded instruction
    | condbr condition left leftArgs right rightArgs =>
      exact edge_below (edge_below bounded instruction.1) instruction.2
    | _ => exact bounded

theorem provenance_below {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov}
    (closed : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionRootsClosed res vt func upper inst)
    (start : ProvenanceBelow (provStart vt func) upper) (rootCount : Nat) :
    ProvenanceBelow (func.provenance res vt rootCount) upper :=
  provFix_below (fun _ bounded => provRound_below closed bounded) start _

end Goose.Lower.Validation.SummaryPreservation
