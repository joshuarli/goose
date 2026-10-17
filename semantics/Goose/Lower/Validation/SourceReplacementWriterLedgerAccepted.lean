import Goose.Lower.Validation.SourceReplacementWriterLedgerEmissions
import Goose.Lower.Validation.SourceReplacementWriterTypingAccepted
import Goose.Lower.Validation.SourceReplacementLexicalWritersTraversal
import Goose.Lower.Validation.SummaryPreservationReplayFinished
import Goose.Lower.Validation.SourceOccurrenceFinishContext
import Goose.Lower.Validation.SourceOccurrenceFinishEntry
import Goose.Lower.Validation.ReplacementSourceSitesBuilder

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open SourceReplacementLexicalWriters SourceReplacementWriterTyping

def contextFragment (module : Core.Module) (impl : Impl) : Fragment :=
  .block none (contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList)) false impl.body

def contextInitial (module : Core.Module) (impl : Impl) : LS :=
  entryReplayState (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    (lowerEnv module impl.vars impl.results.toList)

theorem contextFragment_finish (module : Core.Module) (impl : Impl) :
    cfg_implState module impl =
      (finishFunction impl
        (lowerBlock none (contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList)) false impl.body
          (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)).1
        (lowerEnv module impl.vars impl.results.toList)
        ((contextFragment module impl).finish (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl))).2 := by
  simp only [cfg_implState,cfg_implAction,bind_run,setCur_run,contextFragment,Fragment.finish,
    contextInitial,contextEntryBindings,entryReplayState]

theorem contextFragment_continuation (module : Core.Module) (context : Context) (impl : Impl) :
    NativeBuilderContinuation (lowerContextAt module context impl)
      ((contextFragment module impl).finish (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)) := by
  apply NativeBuilderContinuation.context
  rw [contextFragment_finish]
  exact (advB_finishFunction _ _ _ _ _ _ rfl).ext

theorem contextInitial_liveBound (module : Core.Module) (impl : Impl) : LiveBound (contextInitial module impl) :=
  (entryReplayState_generated _ _).live

theorem context_instruction_source_of_body {module : Core.Module} {context : Context} {impl : Impl}
    (body : EmitsOnly (InstructionSource (contextFragment module impl)
      (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl))
      (contextInitial module impl)
      ((contextFragment module impl).finish (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)))
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instMember : instruction ∈ block.insts) :
    InstructionSource (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) instruction := by
  have entry := entryReplayState_emitsOnly
    (InstructionSource (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl))
    (impl.params.toList.map fun param => .data (tyOfVar impl param.var)) (lowerEnv module impl.vars impl.results.toList)
  have finish := finishFunction_emitsOnly (property := InstructionSource (contextFragment module impl)
    (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)) impl
    (lowerBlock none (contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList)) false impl.body
      (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)).1
    (by intro term writer; exact False.elim writer)
  have whole : EmitsOnly (InstructionSource (contextFragment module impl)
      (lowerEnv module impl.vars impl.results.toList) (contextInitial module impl)) initState (cfg_implState module impl) := by
    rw [contextFragment_finish]
    exact (entry.trans body).trans (finish _ _ _ _ rfl)
  have native := finishBlocks_instruction_member (cfg_context_blocks module context impl ▸ blockMember) instMember
  rcases whole.members native with initial | source
  · simp [initState,LS.insts] at initial
  · exact source

theorem context_cursor_typed {module : Core.Module} {impl : Impl} {implId : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implId]? = some impl)
    {path : List Nat} {fragment : Fragment} {before : LS}
    (located : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) path fragment before) :
    ∃ env scopes, lexicalScopes? (.block impl.body) path = some scopes ∧
      env.mod = module ∧ env.vars = impl.vars ∧ env.impl = some impl ∧ env.scopes = scopes.reverse ∧
      StorageWalkVisible env (ownScopeKeys fragment.node ++ scopes) ∧ NodeTyped env fragment.node :=
  accepted_implementation_node_typed accepted implAt (sourceLoweringAt_source located)

#print axioms contextFragment_continuation
#print axioms context_instruction_source_of_body
#print axioms context_cursor_typed

end Goose.Lower.Validation.SourceReplacementWriterLedger
