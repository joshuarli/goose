import Goose.Lower.Validation.SummaryPreservationBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure BuilderRootWitness (res : Array (List RootRef)) (vt : Array (Option VTy))
    (func : Func) (upper : Prov) (ls : LS) : Prop where
  valueSize : upper.vals.size = ls.vals.size
  instructions : ∀ inst ∈ ls.insts,
    InstructionRootsClosed res vt { func with blocks := finishBlocks ls.blocks } upper inst

theorem emitDef_root_witness_growth {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls final : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} {op : Op} {value : ValueId}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      rootsAt next.vals value = rootsOfDef res vt func upper value op ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [emitDef_run op le current] at run
  cases run
  let partialFunc := { func with blocks := finishBlocks ls.blocks }
  let fresh := rootsOfDef res vt partialFunc upper upper.vals.size op
  let next : Prov := { upper with vals := upper.vals.push fresh }
  have useBounds : ∀ used ∈ op.uses, used < upper.vals.size := by
    intro used member
    rw [witness.valueSize]
    exact uses used member
  have prior := builder_instruction_roots_after_push (newRoots := fresh) symbols
    witness.valueSize (func := partialFunc) rfl witness.instructions
  have appended := appendInst_block_parameters func ls block (.def ls.vals.size op)
  have freshClosed := def_roots_closed_after_push (res := res) (vt := vt) (func := partialFunc) useBounds
  refine ⟨next, ⟨?_, ?_⟩, ?_, rfl, ?_⟩
  · simp [next, witness.valueSize]
  · intro inst member
    have membership : inst ∈ ls.insts ++ [.def ls.vals.size op] :=
      (LS.insts.modifyPush blockBound (.def ls.vals.size op)).mem_iff.mp member
    apply instruction_roots_closed_function_shape (before := partialFunc)
      (after := { func with blocks := finishBlocks (ls.appendInst block (.def ls.vals.size op)).blocks })
      rfl rfl appended
    rcases List.mem_append.mp membership with old | added
    · exact prior inst old
    · have same := List.mem_singleton.mp added
      subst inst
      simpa only [next, fresh, witness.valueSize] using freshClosed
  · change rootsAt (upper.vals.push fresh) ls.vals.size = _
    rw [← witness.valueSize, rootsAt_push_new]
    exact rootsOfDef_function_shape rfl rfl op

  · intro index bound
    exact rootsAt_push_old bound

theorem emitDef_root_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls final : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} {op : Op} {value : ValueId}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (run : emitDef op le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness res vt func next final ∧
      rootsAt next.vals value = rootsOfDef res vt func upper value op ∧
      next.slots = upper.slots := by
  obtain ⟨next, nextWitness, roots, slots, _⟩ :=
    emitDef_root_witness_growth symbols current blockBound witness uses run
  exact ⟨next, nextWitness, roots, slots⟩

end Goose.Lower.Validation.SummaryPreservation
