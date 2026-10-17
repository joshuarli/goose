import Goose.Lower.Validation.EmittedTypingGeneratedHeaders
import Goose.Lower.Validation.EmittedTypingEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_generated_lowerEach {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before) (regrow : Bool) (owner : Option ValueId) (sampled header counter : ValueId) (headerBound : header < before.blocks.size)
    {current : BlockId} (live : before.cur = some current)
    (counterTyped : before.vals[counter]? = some (some (.data (.int .i64))))
    (lengthTyped : EmittedEachLengthTypes before regrow owner sampled)
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → started.vals[counter]? = some (some (.data (.int .i64))) →
      TypePrefix before started → header < started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    let after := (Goose.Lower.lowerEach regrow owner sampled header counter body le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  let length := Goose.Lower.eachLen regrow owner sampled le before
  have lengthProof := emitted_checked_eachLen builder regrow owner sampled lengthTyped
  have lengthLive : length.2.cur = some current := by
    cases regrow
    · exact live
    · cases source : before.cur with
      | none => rw [live] at source; cases source
      | some block =>
        simp only [length, Goose.Lower.eachLen, reduceIte, emitDef_run _ _ source]
        exact live
  have lengthRow := lengthProof.2 (by rw [lengthLive]; rfl)
  have retainedCounter := (types_eachLen regrow owner sampled le before _ _ rfl) counter (.data (.int .i64)) counterTyped
  have lengthGenerated : GeneratedBuilderState length.2 := generated.eachLen (env := le) regrow owner sampled rfl
  have headerAfter := Nat.lt_of_lt_of_le headerBound (advB_eachLen regrow owner sampled le before _ _ rfl).ext.1
  have output := emitted_checked_generated_lowerRange lengthProof.1 lengthGenerated header headerAfter .i64 counter length.1 lengthLive
    retainedCounter lengthRow body
    (fun depth target initial started builder generated counter prefixProof headerBound targetBound =>
      bodyChecked depth target initial started builder generated counter
        ((types_eachLen regrow owner sampled le before _ _ rfl).trans prefixProof) headerBound targetBound)
    bodyAdvance bodyTypes
  exact output

theorem emitted_checked_generated_eachHeader {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before) (regrow : Bool) (owner : Option ValueId) (sampled start : ValueId)
    (startTyped : before.vals[start]? = some (some (.data (.int .i64))))
    (lengthTyped : EmittedEachLengthTypes before regrow owner sampled)
    (body : BlockId → ValueId → Nat → BlockId → B ValueId)
    (bodyChecked : ∀ header counter depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → started.vals[counter]? = some (some (.data (.int .i64))) →
      TypePrefix before started → header < started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body header counter depth target le started).2 ∧
      GeneratedBuilderState (body header counter depth target le started).2)
    (bodyAdvance : ∀ header counter depth target, AdvB (body header counter depth target))
    (bodyTypes : ∀ header counter depth target, TypeRun (body header counter depth target)) :
    let after := ((do
      let (header, params) ← Goose.Lower.newBlock [.data (.int .i64)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [start])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerEach regrow owner sampled header counter (body header counter) : B Unit) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
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
  have allocatedGenerated : GeneratedBuilderState allocated.2 := generated.newBlock (env := le) [.data (.int .i64)] rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have closedGenerated : GeneratedBuilderState closed.2 := allocatedGenerated.emitTerm (env := le) (.br allocated.1.1 [start])
    (by simpa [Term.successors] using fresh) rfl
  have headerClosed : allocated.1.1 < closed.2.blocks.size :=
    Nat.lt_of_lt_of_le fresh (advB_emitTerm (.br allocated.1.1 [start]) le allocated.2 _ _ rfl).ext.1
  have selection : ∀ block, some allocated.1.1 = some block → block < closed.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact headerClosed
  have startedGenerated : GeneratedBuilderState started.2 := closedGenerated.setCur (env := le) _ selection rfl
  have output := emitted_checked_generated_lowerEach startedBuilder startedGenerated regrow owner sampled allocated.1.1 counter headerClosed live
    counterTyped retainedLength (body allocated.1.1 counter)
    (fun depth target initial started builder generated counterTyped prefixProof headerBound targetBound =>
      bodyChecked allocated.1.1 counter depth target initial started builder generated counterTyped
        (headerTypes.trans prefixProof) headerBound targetBound)
    (bodyAdvance allocated.1.1 counter) (bodyTypes allocated.1.1 counter)
  simpa only [bind_run, allocated, counter, closed, started] using output

end Goose.Lower.Validation
