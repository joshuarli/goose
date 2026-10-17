import Goose.Lower.Validation.SourceReplacementLexicalWritersCanonical
import Goose.Lower.Validation.SourceReplacementLexicalWritersInactive
import Goose.Lower.Validation.SourceReplacementWriterLedgerAcceptedWriters
import Goose.Lower.Validation.SourceReplacementWriterLedgerShapes
import Goose.Lower.Validation.SourceReplacementWriterLedgerPrebindings

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR SourceReplacementWriterLedger SourceReplacementWriterTyping

section Context

variable {module : Core.Module} {context : Context} {impl : Impl} {contextIndex : ContextId}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : ReplacementContentFlowSource.SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

theorem context_slotInit_interval_of_accepted
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {replacementPath rhsPath : List Nat}
    (source : DemandNodeAt (.block impl.body) replacementPath
      (.statement (.assignWhole site.source.site.source.place site.source.site.source.rhs origin)))
    (demand : ReplacementDemandContext module contextIndex replacementPath
      site.source.site.source.place site.source.site.source.rhs origin)
    (rhsAt : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) rhsPath (.expression site.source.site.source.rhs)
      site.source.site.source.site.cleared)
    {tracked : VarId} {localVar : LocalVar} (variableAt : impl.vars[tracked]? = some localVar)
    (used : tracked ∈ site.source.site.source.rhs.variables)
    (inactive : tracked ∉ demand.statement.expected.frame.active)
    {block : GIR.Block} (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value : ValueId} {sourceOrigin : Option OriginId}
    (instMember : Inst.eff (.slotInit tracked value sourceOrigin) ∈ block.insts) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨path,fragment,before,event,typing,scopes,located,member,same,stack,
    moduleEq,varsEq,implEq,scopesEq,visible,typed,_⟩ :=
    context_native_writer accepted implAt blockMember instMember (by trivial)
  have active : localVar.scope ∈ ownScopeKeys fragment.node ++ scopes := by
    rcases Fragment.slot_initialization_emission_shape member same with direct | binding
    · obtain ⟨loop,expression,sourceOrigin,rfl,_⟩ := direct
      obtain ⟨scope,output,start,finish,scopeActive,statementTyped⟩ := typed.statement_typing
      obtain ⟨declared,childType,childStart,declaration,_⟩ := tyStmt_let_children statementTyped
      have declaredFacts := declare_ok _ _ _ _ _ declaration
      have sameVar : declared = localVar := by
        have row := declaredFacts.2.1
        rw [varsEq,variableAt] at row
        exact Option.some.inj row.symm
      have sameScope : localVar.scope = scope := sameVar ▸ declaredFacts.2.2.1
      rw [scopesEq] at scopeActive
      have member : scope ∈ scopes := by simpa only [List.mem_reverse] using scopeActive
      exact List.mem_append_right _ (sameScope ▸ member)
    · obtain ⟨loop,bindings,want,body,sourceOrigin,rfl,bindingMember,_⟩ := binding
      have scopeEq := context_block_prebinding_scope_of_row accepted implAt located bindingMember variableAt
      cases body
      simp [scopeEq,Fragment.node,ownScopeKeys,Core.Block.scope]
  have nested := inactive_rhs_writer_scope_prefix accepted contextAt implAt source demand
    (by rfl) rhsAt located stack variableAt used inactive active
  exact canonical_writer_slotInit_source_interval site rhsAt located nested member same

end Context

#print axioms context_slotInit_interval_of_accepted

end Goose.Lower.Validation.SourceReplacementLexicalWriters
