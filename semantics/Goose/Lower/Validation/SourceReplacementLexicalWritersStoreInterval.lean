import Goose.Lower.Validation.SourceReplacementLexicalWritersSlotInit
import Goose.Lower.Validation.SourceReplacementLexicalWritersStores
import Goose.Lower.Validation.SourceReadyCanonicalInputs
import Goose.Lower.Validation.SourceReplacementWriterLedgerChildGeneratedPath
import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesPath

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR SourceReplacementWriterLedger SourceReplacementWriterTyping
open ReplacementContentFlowSource SummaryPreservation

section Context

variable {module : Core.Module} {context : Context} {impl : Impl} {contextIndex : ContextId}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

theorem context_store_interval_of_accepted
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
    {address value : Nat} {sourceOrigin : Option OriginId}
    (instMember : Inst.eff (.store address value sourceOrigin) ∈ block.insts)
    (reference : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true)
    (trackedMember : RootRef.local tracked ∈ rootsAt
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals address) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨facts,sourceEq,rootEq,functionEq,typesEq,provenanceEq,completedEq,_⟩ :=
    accepted_context_ready_inputs accepted contextAt implAt
  have actualBlock : block ∈ facts.func.blocks.toList := by rw [functionEq]; exact blockMember
  have nativeReference : valRefLike facts.types value = true := by rw [typesEq]; exact reference
  have actualTracked : RootRef.local tracked ∈ rootsAt facts.provenance.vals address := by
    rw [provenanceEq]
    exact trackedMember
  have actualUpper := store_tracked_local_upper facts actualBlock instMember nativeReference actualTracked
  obtain ⟨path,fragment,before,event,typing,scopes,located,member,same,stack,
    moduleEq,varsEq,implEq,scopesEq,visible,typed,_⟩ :=
    context_native_writer accepted implAt blockMember instMember (by trivial)
  have tables : SourceRootTables typing facts.source := by
    constructor
    · simpa only [sourceEq] using moduleEq.symm
    · simpa only [sourceEq] using varsEq.symm
  have nativeFinal : NativeRows facts.types (cfg_implState module impl) := by
    rw [typesEq,lowerContext_valueTypes_of_accepted accepted implAt]
    exact NativeRows.refl _
  have rootTypes : TypePrefix
      ((contextFragment module impl).finish (lowerEnv module impl.vars impl.results.toList)
        (contextInitial module impl)) (cfg_implState module impl) := by
    rw [contextFragment_finish]
    exact ReplayBuilder.types_finishFunction _ _ _ _ _ _ rfl
  have nativeFragment : NativeRows facts.types
      (fragment.finish (lowerEnv typing.mod typing.vars impl.results.toList) before) := by
    rw [moduleEq,varsEq]
    exact nativeFinal.of_prefix (located.typePrefix.2.trans rootTypes)
  have continuation : NativeBuilderContinuation facts.func
      (fragment.finish (lowerEnv typing.mod typing.vars impl.results.toList) before) := by
    rw [functionEq,moduleEq,varsEq]
    exact (contextFragment_continuation module context impl).of_extension located.span.2
  have actualMember : event ∈ fragment.emissions (lowerEnv typing.mod typing.vars impl.results.toList) before := by
    rw [moduleEq,varsEq]
    exact member
  have trackedVisible := store_emission_tracked_visible facts tables typed
    (context_cursor_generated located).1 nativeFragment continuation actualMember same nativeReference actualUpper
  have nested := inactive_rhs_visible_writer_prefix accepted contextAt implAt source demand
    (by rfl) rhsAt located stack varsEq visible variableAt used inactive trackedVisible
  exact canonical_writer_store_source_interval site rhsAt located nested member same

end Context

#print axioms context_store_interval_of_accepted

end Goose.Lower.Validation.SourceReplacementLexicalWriters
