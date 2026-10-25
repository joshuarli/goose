import Goose.Lower.Validation.SourceReplacementLexicalWriters
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.Entry

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core SourceCanonicalRootFloors

theorem accepted_implementation_writer_localization {module : Core.Module} {index : ImplId} {impl : Impl}
    {rhs : Expr} {writer : DemandNode} {rhsPath writerPath scopes : List Nat} {scope : Nat}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[index]? = some impl)
    (rhsAt : DemandNodeAt (.block impl.body) rhsPath (.expression rhs))
    (writerAt : DemandNodeAt (.block impl.body) writerPath writer)
    (stackAt : lexicalScopes? (.block impl.body) writerPath = some scopes)
    (active : scope ∈ scopes) (fresh : scope ∈ sourceNodeScopeKeys (.expression rhs)) :
    rhsPath <+: writerPath := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))
  exact lexical_scope_writer_localization (sourceRootScopeValid_block checked).1
    rhsAt writerAt stackAt active fresh

theorem accepted_global_writer_localization {module : Core.Module} {index : GlobalId} {global : Core.Global}
    {rhs : Expr} {writer : DemandNode} {rhsPath writerPath scopes : List Nat} {scope : Nat}
    (accepted : Core.validate module = .ok ()) (globalAt : module.globals[index]? = some global)
    (rhsAt : DemandNodeAt (.expression global.init) rhsPath (.expression rhs))
    (writerAt : DemandNodeAt (.expression global.init) writerPath writer)
    (stackAt : lexicalScopes? (.expression global.init) writerPath = some scopes)
    (active : scope ∈ scopes) (fresh : scope ∈ sourceNodeScopeKeys (.expression rhs)) :
    rhsPath <+: writerPath :=
  lexical_scope_writer_localization (sourceRootScopeValid_global (validate_global_checks accepted globalAt)).1
    rhsAt writerAt stackAt active fresh

theorem accepted_implementation_writer_source {module : Core.Module} {index : ImplId} {impl : Impl}
    {rhs : Expr} {writer : DemandNode} {rhsPath writerPath scopes : List Nat} {scope : Nat}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[index]? = some impl)
    (rhsAt : DemandNodeAt (.block impl.body) rhsPath (.expression rhs))
    (writerAt : DemandNodeAt (.block impl.body) writerPath writer)
    (stackAt : lexicalScopes? (.block impl.body) writerPath = some scopes)
    (active : scope ∈ scopes) (fresh : scope ∈ sourceNodeScopeKeys (.expression rhs)) :
    ∃ suffix, writerPath = rhsPath ++ suffix ∧ DemandNodeAt (.expression rhs) suffix writer :=
  source_path_suffix rhsAt writerAt
    (accepted_implementation_writer_localization accepted implAt rhsAt writerAt stackAt active fresh)

#print axioms accepted_implementation_writer_localization
#print axioms accepted_global_writer_localization
#print axioms accepted_implementation_writer_source

end Goose.Lower.Validation.SourceReplacementLexicalWriters
