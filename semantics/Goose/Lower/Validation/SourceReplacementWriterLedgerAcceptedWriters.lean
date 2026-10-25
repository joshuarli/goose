import Goose.Lower.Validation.SourceReplacementWriterLedgerAccepted
import Goose.Lower.Validation.SourceReplacementWriterLedgerInduction
import Goose.Lower.Validation.SourceReplacementLexicalWritersEmissionSpans

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open SourceReplacementLexicalWriters SourceReplacementWriterTyping

theorem context_instruction_source {module : Core.Module} {context : Context} {impl : Impl}
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instMember : instruction ∈ block.insts) :
    InstructionSource (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) instruction :=
  context_instruction_source_of_body (source_instruction_ledger _ _ _) blockMember instMember

theorem context_native_writer {module : Core.Module} {context : Context} {impl : Impl} {implId : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implId]? = some impl)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instMember : instruction ∈ block.insts) (writer : WriterInstruction instruction) :
    ∃ path fragment before emission env scopes,
      SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
        (contextInitial module impl) path fragment before ∧
      emission ∈ fragment.emissions (lowerEnv module impl.vars impl.results.toList) before ∧
      emission.instruction = instruction ∧
      lexicalScopes? (.block impl.body) path = some scopes ∧
      env.mod = module ∧ env.vars = impl.vars ∧ env.impl = some impl ∧ env.scopes = scopes.reverse ∧
      StorageWalkVisible env (ownScopeKeys fragment.node ++ scopes) ∧ NodeTyped env fragment.node ∧
      LiveBound before ∧ LiveBound emission.before ∧
      emission.Run (lowerEnv module impl.vars impl.results.toList) ∧
      before.Ext emission.before ∧
      emission.after.Ext (fragment.finish (lowerEnv module impl.vars impl.results.toList) before) ∧
      NativeBuilderContinuation (lowerContextAt module context impl) emission.after := by
  obtain ⟨path,fragment,before,emission,located,member,same⟩ :=
    context_instruction_source blockMember instMember writer
  obtain ⟨env,scopes,stack,modEq,varsEq,implEq,scopesEq,visible,typed⟩ :=
    context_cursor_typed accepted implAt located
  have bounded := located.liveBound (contextInitial_liveBound module impl)
  have localSpan := fragment_emission_span member
  refine ⟨path,fragment,before,emission,env,scopes,located,member,same,stack,
    modEq,varsEq,implEq,scopesEq,visible,typed,bounded,
    fragment_emission_liveBound bounded member,Fragment.emission_run member,
    localSpan.1,localSpan.2,?_⟩
  exact (contextFragment_continuation module context impl).of_extension
    (localSpan.2.trans located.span.2)

#print axioms context_instruction_source
#print axioms context_native_writer

end Goose.Lower.Validation.SourceReplacementWriterLedger
