import Goose.Lower.Validation.EmittedTypingGeneratedLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_generated_whileHeader {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (condition : B ValueId) (body : BlockId → Nat → BlockId → B ValueId)
    (conditionChecked : ∀ initial before, EmittedBuilder le initial before → GeneratedBuilderState before →
      EmittedBuilder le initial (condition le before).2 ∧ GeneratedBuilderState (condition le before).2)
    (conditionBound : ValueRun condition) (conditionAdvance : AdvB condition)
    (bodyChecked : ∀ header depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → header < started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body header depth target le started).2 ∧ GeneratedBuilderState (body header depth target le started).2)
    (bodyAdvance : ∀ header depth target, AdvB (body header depth target))
    (bodyTypes : ∀ header depth target, TypeRun (body header depth target)) :
    let after := ((do
      let (header, _) ← Goose.Lower.newBlock []
      Goose.Lower.emitTerm (.br header [])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerWhile header condition (body header) : B Unit) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  let allocated := Goose.Lower.newBlock [] le before
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2
  let started := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedBuilder := builder.newBlock []
  have allocatedGenerated : GeneratedBuilderState allocated.2 := generated.newBlock (env := le) [] rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have closedBuilder := allocatedBuilder.emitTerm (.br allocated.1.1 [])
    (by intro active value member; simp [Term.uses] at member)
  have closedGenerated : GeneratedBuilderState closed.2 := allocatedGenerated.emitTerm (env := le) (.br allocated.1.1 [])
    (by simpa [Term.successors] using fresh) rfl
  have headerBound : allocated.1.1 < closed.2.blocks.size :=
    Nat.lt_of_lt_of_le fresh (advB_emitTerm (.br allocated.1.1 []) le allocated.2 _ _ rfl).ext.1
  have selectedBound : ∀ block, some allocated.1.1 = some block → block < closed.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact headerBound
  have startedBuilder := closedBuilder.setCur (some allocated.1.1) selectedBound
  have startedGenerated : GeneratedBuilderState started.2 := closedGenerated.setCur (env := le) _ selectedBound rfl
  have headerStarted : allocated.1.1 < started.2.blocks.size := headerBound
  have checked := emitted_checked_generated_lowerWhile startedBuilder startedGenerated allocated.1.1 headerStarted
    condition (body allocated.1.1) conditionChecked conditionBound conditionAdvance
    (bodyChecked allocated.1.1) (bodyAdvance allocated.1.1) (bodyTypes allocated.1.1)
  simpa only [bind_run, allocated, closed, started] using checked

theorem emitted_checked_generated_rangeHeader {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before) (type : IntTy) (lower upper : ValueId)
    (lowerTyped : before.vals[lower]? = some (some (.data (.int type))))
    (upperTyped : before.vals[upper]? = some (some (.data (.int type))))
    (body : BlockId → ValueId → Nat → BlockId → B ValueId)
    (bodyChecked : ∀ header counter depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → started.vals[counter]? = some (some (.data (.int type))) →
      TypePrefix before started → header < started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body header counter depth target le started).2 ∧
      GeneratedBuilderState (body header counter depth target le started).2)
    (bodyAdvance : ∀ header counter depth target, AdvB (body header counter depth target))
    (bodyTypes : ∀ header counter depth target, TypeRun (body header counter depth target)) :
    let after := ((do
      let (header, params) ← Goose.Lower.newBlock [.data (.int type)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [lower])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerRange type counter upper header (body header counter) : B Unit) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  let allocated := Goose.Lower.newBlock [.data (.int type)] le before
  let counter := allocated.1.2.headD 0
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 [lower]) le allocated.2
  let started := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedBuilder := builder.newBlock [.data (.int type)]
  have closedBuilder := allocatedBuilder.emitTerm (.br allocated.1.1 [lower]) (by
    intro active value member
    have same : value = lower := by simpa [Term.uses] using member
    subst value
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp lowerTyped).1
      (emittedTypePrefix_newBlock [.data (.int type)] le before).size)
  have startedBuilder := closedBuilder.setCur (some allocated.1.1) (by
    intro block same
    have id : block = before.blocks.size := (Option.some.inj same).symm
    subst block
    have size := (advB_emitTerm (.br allocated.1.1 [lower]) le allocated.2 _ _ rfl).ext.1
    have fresh : before.blocks.size < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
    exact Nat.lt_of_lt_of_le fresh size)
  have allocatedCounter : allocated.2.vals[counter]? = some (some (.data (.int type))) := by
    have row := newBlock_parameter_types [.data (.int type)] le before 0
    simpa only [allocated, counter, newBlock1_run, List.headD, List.head?, Option.getD_some, Nat.add_zero,
      List.getElem?_cons_zero, Option.map_some] using row
  have retained := (types_emitTerm (.br allocated.1.1 [lower]) le allocated.2 _ _ rfl).trans
    (types_setCur (some allocated.1.1) le closed.2 _ _ rfl)
  have counterTyped := retained counter (.data (.int type)) allocatedCounter
  have retainedUpper := retained upper (.data (.int type))
    ((emittedTypePrefix_newBlock [.data (.int type)] le before).typed upper (.data (.int type)) upperTyped)
  have live : started.2.cur = some allocated.1.1 := rfl
  have headerTypes := (types_newBlock [.data (.int type)] le before _ _ rfl).trans retained
  have allocatedGenerated : GeneratedBuilderState allocated.2 := generated.newBlock (env := le) [.data (.int type)] rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have closedGenerated : GeneratedBuilderState closed.2 := allocatedGenerated.emitTerm (env := le) (.br allocated.1.1 [lower])
    (by simpa [Term.successors] using fresh) rfl
  have headerClosed : allocated.1.1 < closed.2.blocks.size :=
    Nat.lt_of_lt_of_le fresh (advB_emitTerm (.br allocated.1.1 [lower]) le allocated.2 _ _ rfl).ext.1
  have selection : ∀ block, some allocated.1.1 = some block → block < closed.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact headerClosed
  have startedGenerated : GeneratedBuilderState started.2 := closedGenerated.setCur (env := le) _ selection rfl
  have output := emitted_checked_generated_lowerRange startedBuilder startedGenerated allocated.1.1 headerClosed type counter upper live
    counterTyped retainedUpper (body allocated.1.1 counter)
    (fun depth target initial started builder generated counterTyped prefixProof headerBound targetBound =>
      bodyChecked allocated.1.1 counter depth target initial started builder generated counterTyped
        (headerTypes.trans prefixProof) headerBound targetBound)
    (bodyAdvance allocated.1.1 counter) (bodyTypes allocated.1.1 counter)
  simpa only [bind_run, allocated, counter, closed, started] using output

end Goose.Lower.Validation
