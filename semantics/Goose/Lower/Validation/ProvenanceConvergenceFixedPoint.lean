import Goose.Lower.Validation.ProvenanceConvergenceUniverse

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.GIR

theorem provFix_bounded {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (fuel : Nat) {provenance : Prov} (bound : Bounded roots provenance) :
    Bounded roots (provFix results types func fuel provenance) := by
  induction fuel generalizing provenance with
  | zero => exact bound
  | succ fuel ih =>
    change Bounded roots (if (provRound results types func provenance).2 then
      provFix results types func fuel (provRound results types func provenance).1
      else (provRound results types func provenance).1)
    split
    · exact ih (provRound_bounded universeBound bound)
    · exact provRound_bounded universeBound bound

theorem provFix_quiet {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (fuel capacity : Nat) {provenance : Prov} (bound : Bounded roots provenance)
    (capacityBound : (provenance.slots.size + provenance.vals.size) * roots.length ≤ capacity)
    (enough : capacity < weight provenance + fuel) :
    (provRound results types func (provFix results types func fuel provenance)).2 = false := by
  induction fuel generalizing provenance with
  | zero =>
    have limited := bound.weight_le
    omega
  | succ fuel ih =>
    by_cases changed : (provRound results types func provenance).2 = true
    · simp only [provFix, changed, ite_true]
      have growth := provRound_growth results types func provenance
      apply ih (provRound_bounded universeBound bound)
      · simpa only [growth.slots, growth.vals] using capacityBound
      · have strict : weight provenance < weight (provRound results types func provenance).1 := growth.strict rfl changed
        omega
    · have quiet : (provRound results types func provenance).2 = false := Bool.eq_false_iff.mpr changed
      have same := provRound_quiet results types func provenance quiet
      simpa only [provFix, quiet, Bool.false_eq_true, ite_false, same] using quiet

theorem provenance_quiet {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (rootCount : Nat) (rootBound : roots.length ≤ rootCount) :
    (provRound results types func (func.provenance results types rootCount)).2 = false := by
  unfold Func.provenance
  apply provFix_quiet universeBound _ ((func.numValues + func.slots.size) * roots.length)
    (provStart_bounded universeBound)
  · simp only [provStart_values_size]
    simp [provStart, Nat.add_comm]
  · have product := Nat.mul_le_mul_left (func.numValues + func.slots.size) rootBound
    have enough : (func.numValues + func.slots.size) * roots.length <
        (func.numValues + func.slots.size + 1) * (rootCount + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at product ⊢
      omega
    omega

theorem provenance_fixed {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (rootCount : Nat) (rootBound : roots.length ≤ rootCount) :
    provRound results types func (func.provenance results types rootCount) =
      (func.provenance results types rootCount, false) :=
  provRound_quiet results types func _ (provenance_quiet universeBound rootCount rootBound)

theorem provenance_instructionRootsClosed {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (rootCount : Nat) (rootBound : roots.length ≤ rootCount) :
    InstructionRootsClosed results types func (func.provenance results types rootCount) :=
  instructionRootsClosed_of_quiet (provenance_quiet universeBound rootCount rootBound)

theorem InstructionRootsClosed.definition {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {provenance : Prov}
    (closed : InstructionRootsClosed results types func provenance)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {value : ValueId} {op : Op} (member : Inst.def value op ∈ block.insts)
    (bounded : value < provenance.vals.size) :
    rootsOfDef results types func provenance value op ⊆ rootsAt provenance.vals value := by
  intro root produced
  have inserted := addTo_inserts bounded produced
  have same := congrArg (fun state : Prov × Bool => state.1.vals) (closed block blockMember _ member)
  change (GIR.addTo provenance.vals value (rootsOfDef results types func provenance value op)).1 = provenance.vals at same
  rw [same] at inserted
  exact inserted

theorem InstructionRootsClosed.slotInit {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {provenance : Prov}
    (closed : InstructionRootsClosed results types func provenance)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {slot : SlotId} {value : ValueId} {origin : OriginId}
    (member : Inst.eff (.slotInit slot value origin) ∈ block.insts)
    (bounded : slot < provenance.slots.size) :
    rootsAt provenance.vals value ⊆ rootsAt provenance.slots slot := by
  intro root produced
  have inserted := addTo_inserts bounded produced
  have same := congrArg (fun state : Prov × Bool => state.1.slots) (closed block blockMember _ member)
  change (GIR.addTo provenance.slots slot (rootsAt provenance.vals value)).1 = provenance.slots at same
  rw [same] at inserted
  exact inserted

end Goose.Lower.Validation.ProvenanceConvergence
