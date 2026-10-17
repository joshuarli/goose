import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.SourceReadyObservations
import Goose.Lower.Validation.SummaryPreservationReplayFinished

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.normalized_operands (facts : SourceReadyFunction)
    (ready : SourceReadyBuilder facts.state facts.completed)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value : ValueId} (use : value ∈ instruction.uses) :
    ∃ roots, normalize facts.func (flowAt facts.state.values value) = some roots := by
  have bounded : value < facts.state.values.size := by
    rw [facts.canonical.shape.values]
    exact facts.native.uses block blockMember instruction instructionMember value use
  have selected := facts.canonical.values value bounded
  have emitted := finishBlocks_instruction_member
    (facts.frame.blocks ▸ blockMember) instructionMember
  obtain ⟨roots, known, _⟩ := selected.actual facts.native.roots.closed
    ((ready instruction emitted).1 value use)
  exact ⟨roots, known⟩

theorem SourceReadyFunction.write_safety (facts : SourceReadyFunction)
    {index : Nat} {roots : Roots}
    (written : facts.state.writes[index]? = some (.assigned roots)) :
    roots = .pending ∨ ∃ actual, normalize facts.func roots = some actual := by
  by_cases pending : roots = .pending
  · exact Or.inl pending
  · apply Or.inr
    have bounded := (Array.getElem?_eq_some_iff.mp written).1
    have selected := facts.canonical.memory.writes index bounded
    simp only [written, Option.getD_some, Write.SymbolicRefine] at selected
    obtain ⟨actual, known, _⟩ := selected.actual facts.native.roots.closed pending
    exact ⟨actual, known⟩

theorem SourceReadyFunction.call_arity (facts : SourceReadyFunction)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value calleeId : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ callee, (lower facts.source.mod).funcs[calleeId]? = some callee ∧
      arguments.length = callee.params.length := by
  obtain ⟨site⟩ := facts.native.calls block blockMember value calleeId arguments origin called
  refine ⟨site.callee, site.calleeAt, ?_⟩
  have native := facts.native.typing block blockMember _ called
  cases native with
  | definition _ _ type typed recorded =>
    have signature : ({(lower facts.source.mod).tyEnv facts.func with vals := facts.types} : TyEnv).sigs[calleeId]? =
        some (site.callee.params, site.callee.results) := by
      change ((lower facts.source.mod).funcs.map fun callee => (callee.params, callee.results))[calleeId]? = _
      simp only [Array.getElem?_map, site.calleeAt, Option.map_some]
    by_cases arity : site.callee.params.length = arguments.length
    · exact arity.symm
    · simp [Op.resultTy, signature, arity, bind, Except.bind, tyErr] at typed

theorem SourceReadyFunction.observed_contents (facts : SourceReadyFunction)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value calleeId : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    {callee : Func} (calleeAt : (lower facts.source.mod).funcs[calleeId]? = some callee)
    {index argument : Nat}
    (declared : (callee.roots.contents.find? (·.1 == index)).isSome = true)
    (argumentAt : arguments[index]? = some argument) :
    content facts.func facts.state (flowAt facts.state.values argument) ≠ .pending := by
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ blockMember) called
  have available := observed _ emitted value calleeId arguments origin rfl callee calleeAt
  cases row : callee.roots.contents.find? (·.1 == index) with
  | none => simp [row] at declared
  | some pair =>
    have same : pair.1 = index := by simpa only [beq_iff_eq] using Array.find?_some row
    rcases pair with ⟨parameter, ceiling⟩
    dsimp only at same
    subst parameter
    have type := (facts.moduleFacts.functions calleeId callee calleeAt).roots.contentTypes index ceiling row
    have bound : index < callee.params.length := by
      cases parameterRow : callee.params[index]? with
      | none => simp [parameterRow] at type
      | some parameter => exact (List.getElem?_eq_some_iff.mp parameterRow).1
    obtain ⟨selected, roots, selectedAt, known⟩ := available.contents index ceiling bound row
    have identity : selected = argument := Option.some.inj (selectedAt.symm.trans argumentAt)
    rw [identity] at known
    intro pending
    simp [pending, normalize] at known

#print axioms SourceReadyFunction.normalized_operands
#print axioms SourceReadyFunction.write_safety
#print axioms SourceReadyFunction.call_arity
#print axioms SourceReadyFunction.observed_contents

end Goose.Lower.Validation.ReplacementContentFlowSource
