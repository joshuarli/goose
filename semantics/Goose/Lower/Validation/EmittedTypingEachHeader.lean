import Goose.Lower.Validation.EmittedTypingHeaders
import Goose.Lower.Validation.EmittedTypingEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_eachHeader {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (regrow : Bool) (owner : Option ValueId) (sampled start : ValueId)
    (startTyped : before.vals[start]? = some (some (.data (.int .i64))))
    (lengthTyped : EmittedEachLengthTypes before regrow owner sampled)
    (body : BlockId → ValueId → Nat → BlockId → B ValueId)
    (bodyChecked : ∀ header counter depth target initial started, EmittedBuilder le initial started →
      started.vals[counter]? = some (some (.data (.int .i64))) → TypePrefix before started →
      EmittedBuilder le initial (body header counter depth target le started).2)
    (bodyAdvance : ∀ header counter depth target, AdvB (body header counter depth target))
    (bodyTypes : ∀ header counter depth target, TypeRun (body header counter depth target)) :
    EmittedBuilder le initial ((do
      let (header, params) ← Goose.Lower.newBlock [.data (.int .i64)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [start])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerEach regrow owner sampled header counter (body header counter) : B Unit) le before).2 := by
  let allocated := Goose.Lower.newBlock [.data (.int .i64)] le before
  let counter := allocated.1.2.headD 0
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 [start]) le allocated.2
  let started := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedBuilder := builder.newBlock [.data (.int .i64)]
  have closedBuilder := allocatedBuilder.emitTerm (.br allocated.1.1 [start]) (by
    intro active value member
    have same : value = start := by simpa [Term.uses] using member
    subst value
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp startTyped).1
      (emittedTypePrefix_newBlock [.data (.int .i64)] le before).size)
  have startedBuilder := closedBuilder.setCur (some allocated.1.1) (by
    intro block same
    have id : block = before.blocks.size := (Option.some.inj same).symm
    subst block
    have size := (advB_emitTerm (.br allocated.1.1 [start]) le allocated.2 _ _ rfl).ext.1
    have fresh : before.blocks.size < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
    exact Nat.lt_of_lt_of_le fresh size)
  have allocatedCounter : allocated.2.vals[counter]? = some (some (.data (.int .i64))) := by
    have row := newBlock_parameter_types [.data (.int .i64)] le before 0
    simpa only [allocated, counter, newBlock1_run, List.headD, List.head?, Option.getD_some, Nat.add_zero,
      List.getElem?_cons_zero, Option.map_some] using row
  have retained := (types_emitTerm (.br allocated.1.1 [start]) le allocated.2 _ _ rfl).trans
    (types_setCur (some allocated.1.1) le closed.2 _ _ rfl)
  have counterTyped := retained counter (.data (.int .i64)) allocatedCounter
  have retainedLength := lengthTyped.retained ((types_newBlock [.data (.int .i64)] le before _ _ rfl).trans retained)
  have live : started.2.cur = some allocated.1.1 := rfl
  have headerTypes := (types_newBlock [.data (.int .i64)] le before _ _ rfl).trans retained
  have output := emitted_checked_lowerEach startedBuilder regrow owner sampled allocated.1.1 counter live
    counterTyped retainedLength (body allocated.1.1 counter)
    (fun depth target initial started builder counterTyped prefixProof =>
      bodyChecked allocated.1.1 counter depth target initial started builder counterTyped (headerTypes.trans prefixProof))
    (bodyAdvance allocated.1.1 counter) (bodyTypes allocated.1.1 counter)
  simpa only [bind_run, allocated, counter, closed, started] using output

end Goose.Lower.Validation
