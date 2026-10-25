import Goose.Lower.Validation.SourceReplacementWriterLedgerAcceptedWriters
import Goose.Lower.Validation.SourceReplacementWriterLedgerShapes

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open SourceReplacementLexicalWriters

theorem context_native_replacement_cursor {module : Core.Module} {context : Context} {impl : Impl}
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {owner replacementValue : ValueId} {origin : OriginId}
    (instMember : Inst.eff (.replace owner replacementValue (some origin)) ∈ block.insts) :
    ∃ path loop place rhs before,
      SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
        (contextInitial module impl) path (.statement loop (.assignWhole place rhs origin)) before ∧
      let env := lowerEnv module impl.vars impl.results.toList
      let addressed := lowerPlace place env before
      let cleared := (emitEffect (.clear addressed.1 (some origin)) env addressed.2).2
      let captured := lowerExpr rhs env cleared
      owner = addressed.1 ∧ replacementValue = captured.1 ∧
      SourceLoweringAt (contextFragment module impl) env (contextInitial module impl)
        (path ++ [1]) (.expression rhs) cleared ∧
      NativeBuilderContinuation (lowerContextAt module context impl) captured.2 ∧
      ∃ published, emitEffect (.replace owner replacementValue (some origin)) env captured.2 = ((),published) ∧
        NativeBuilderContinuation (lowerContextAt module context impl) published := by
  obtain ⟨path,fragment,before,emission,located,member,same⟩ :=
    context_instruction_source blockMember instMember (by trivial)
  obtain ⟨loop,place,rhs,sourceOrigin,fragmentEq,originEq,ownerEq,valueEq,capturedEq,publishedRun⟩ :=
    Fragment.replacement_emission_shape member same
  have originSame := Option.some.inj originEq.symm
  subst sourceOrigin
  subst fragment
  have localSpan := fragment_emission_span member
  have publishedContinuation := (contextFragment_continuation module context impl).of_extension
    (localSpan.2.trans located.span.2)
  refine ⟨path,loop,place,rhs,before,located,ownerEq,valueEq,located.replacement_rhs,?_,?_,?_⟩
  · rw [← capturedEq]
    exact publishedContinuation.of_extension (advB_emitEffect _ _ _ _ _ publishedRun).ext
  · exact emission.after
  · exact ⟨by simpa only [capturedEq] using publishedRun,publishedContinuation⟩

#print axioms context_native_replacement_cursor

end Goose.Lower.Validation.SourceReplacementWriterLedger
