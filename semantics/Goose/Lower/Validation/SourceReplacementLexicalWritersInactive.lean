import Goose.Lower.Validation.SourceReplacementLexicalWritersTraversal
import Goose.Lower.Validation.SourceReplacementWriterTypingVariablePaths

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR SourceReplacementWriterLedger SourceCanonicalRootFloors

theorem inactive_rhs_writer_scope_prefix {module : Core.Module} {context : Context} {impl : Impl}
    {contextIndex : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {replacementPath : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (source : DemandNodeAt (.block impl.body) replacementPath (.statement (.assignWhole place rhs origin)))
    (demand : ReplacementDemandContext module contextIndex replacementPath place rhs origin)
    {ownerRoot writer : Fragment} {env : LEnv} {initial rhsBefore writerBefore : LS}
    {rhsPath writerPath scopes : List Nat}
    (rootNode : ownerRoot.node = .block impl.body)
    (rhsAt : SourceLoweringAt ownerRoot env initial rhsPath (.expression rhs) rhsBefore)
    (writerAt : SourceLoweringAt ownerRoot env initial writerPath writer writerBefore)
    (stackAt : lexicalScopes? ownerRoot.node writerPath = some scopes)
    {tracked : VarId} {localVar : LocalVar} (variableAt : impl.vars[tracked]? = some localVar)
    (used : tracked ∈ rhs.variables) (inactive : tracked ∉ demand.statement.expected.frame.active)
    (active : localVar.scope ∈ ownScopeKeys writer.node ++ scopes) : rhsPath <+: writerPath := by
  have fresh := SourceReplacementWriterTyping.accepted_inactive_rhs_variable_scope
    accepted contextAt implAt source demand variableAt used inactive
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))
  have unique : (sourceNodeScopeKeys ownerRoot.node).Nodup := by
    rw [rootNode]
    exact (sourceRootScopeValid_block checked).1
  exact canonical_writer_scope_prefix unique rhsAt writerAt stackAt active fresh

theorem inactive_rhs_visible_writer_prefix {module : Core.Module} {context : Context} {impl : Impl}
    {contextIndex : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {replacementPath : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (source : DemandNodeAt (.block impl.body) replacementPath (.statement (.assignWhole place rhs origin)))
    (demand : ReplacementDemandContext module contextIndex replacementPath place rhs origin)
    {ownerRoot writer : Fragment} {env : LEnv} {initial rhsBefore writerBefore : LS}
    {rhsPath writerPath scopes : List Nat}
    (rootNode : ownerRoot.node = .block impl.body)
    (rhsAt : SourceLoweringAt ownerRoot env initial rhsPath (.expression rhs) rhsBefore)
    (writerAt : SourceLoweringAt ownerRoot env initial writerPath writer writerBefore)
    (stackAt : lexicalScopes? ownerRoot.node writerPath = some scopes)
    {typing : TEnv} (variables : typing.vars = impl.vars)
    (visible : StorageWalkVisible typing (ownScopeKeys writer.node ++ scopes))
    {tracked : VarId} {localVar : LocalVar} (variableAt : impl.vars[tracked]? = some localVar)
    (used : tracked ∈ rhs.variables) (inactive : tracked ∉ demand.statement.expected.frame.active)
    (trackedVisible : tracked ∈ typing.visible) : rhsPath <+: writerPath :=
  inactive_rhs_writer_scope_prefix accepted contextAt implAt source demand rootNode rhsAt writerAt stackAt
    variableAt used inactive (visible tracked localVar trackedVisible (variables ▸ variableAt))

#print axioms inactive_rhs_writer_scope_prefix
#print axioms inactive_rhs_visible_writer_prefix

end Goose.Lower.Validation.SourceReplacementLexicalWriters
