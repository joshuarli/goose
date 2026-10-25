import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteLookup
import Goose.Lower.Validation.StorageWalkSourceFacts

set_option Elab.async false
set_option maxRecDepth 4096

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core SourceCanonicalRootFloors

def ownScopeKeys : DemandNode → List Nat
  | .block (.mk scope _ _) => [scope]
  | _ => []

def childScopeKeys (children : List (Option DemandNode)) : List Nat :=
  children.flatMap fun child => child.toList.flatMap sourceNodeScopeKeys

private theorem exprList_scope_keys (expressions : List Expr) :
    (exprsScopes none expressions).map Prod.fst =
      childScopeKeys (expressions.map (some ∘ DemandNode.expression)) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
    simp only [childScopeKeys] at ih
    simp [exprsScopes,childScopeKeys,sourceNodeScopeKeys,ih]

private theorem argument_scope_keys (arguments : List Arg) :
    (argsScopes none arguments).map Prod.fst = childScopeKeys (arguments.map fun
      | .byVal expression => some (.expression expression)
      | .byRef _ place => some (.place place)) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
    simp only [childScopeKeys] at ih
    cases argument <;> simp [argsScopes,childScopeKeys,sourceNodeScopeKeys,ih]

private theorem statementList_scope_keys (statements : List Stmt) :
    (stmtsScopes none statements).map Prod.fst =
      childScopeKeys (statements.map (some ∘ DemandNode.statement)) := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
    simp only [childScopeKeys] at ih
    simp [stmtsScopes,childScopeKeys,sourceNodeScopeKeys,ih]

private theorem print_scope_keys (arguments : List PrintArg) :
    (printScopes none arguments).map Prod.fst = childScopeKeys (arguments.map fun
      | .text _ => none
      | .expr expression => some (.expression expression)) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
    simp only [childScopeKeys] at ih
    cases argument <;> simp [printScopes,childScopeKeys,sourceNodeScopeKeys,ih]

theorem scope_keys_children (node : DemandNode) :
    sourceNodeScopeKeys node = ownScopeKeys node ++ childScopeKeys node.children := by
  cases node with
  | expression expression =>
    cases expression <;>
      simp [sourceNodeScopeKeys,ownScopeKeys,DemandNode.children,exprScopes,childScopeKeys,
        sourceNodeScopeKeys]
    all_goals first | exact argument_scope_keys _ | exact exprList_scope_keys _
  | place place =>
    cases place <;> simp [sourceNodeScopeKeys,ownScopeKeys,DemandNode.children,placeScopes,childScopeKeys,sourceNodeScopeKeys]
  | view view =>
    cases view <;> simp [sourceNodeScopeKeys,ownScopeKeys,DemandNode.children,viewScopes,childScopeKeys,sourceNodeScopeKeys]
  | bound bound =>
    cases bound <;> simp [sourceNodeScopeKeys,ownScopeKeys,DemandNode.children,boundScopes,childScopeKeys,sourceNodeScopeKeys]
  | statement statement =>
    cases statement <;>
      simp only [sourceNodeScopeKeys] <;>
      rw [stmtScopes.eq_def] <;>
      simp [ownScopeKeys,DemandNode.children,childScopeKeys,sourceNodeScopeKeys]
    all_goals first | exact print_scope_keys _ | (split <;> simp [sourceNodeScopeKeys])
  | block block =>
    cases block with
    | mk scope statements value =>
      cases value <;>
        simp [sourceNodeScopeKeys,ownScopeKeys,DemandNode.children,blockScopes,childScopeKeys,
          sourceNodeScopeKeys,stmtsScopes_keys_none,exprScopes_keys_none]
      all_goals exact statementList_scope_keys _

private theorem child_keys_member {parent child : DemandNode} {index scope : Nat}
    (row : parent.child? index = some child) (member : scope ∈ sourceNodeScopeKeys child) :
    scope ∈ childScopeKeys parent.children := by
  have row : parent.children[index]? = some (some child) := by
    cases found : parent.children[index]? <;> simp_all [DemandNode.child?]
  exact List.mem_flatMap.mpr ⟨some child,List.mem_of_getElem? row,
    List.mem_flatMap.mpr ⟨child,by simp,member⟩⟩

theorem child_keys_subset {parent child : DemandNode} {index : Nat}
    (row : parent.child? index = some child) : sourceNodeScopeKeys child ⊆ sourceNodeScopeKeys parent := by
  intro scope member
  rw [scope_keys_children]
  exact List.mem_append_right _ (child_keys_member row member)

theorem source_keys_subset {root node : DemandNode} {path : List Nat}
    (source : DemandNodeAt root path node) : sourceNodeScopeKeys node ⊆ sourceNodeScopeKeys root := by
  induction source with
  | here => exact List.Subset.refl _
  | child row source ih => exact ih.trans (child_keys_subset row)

private theorem flatMap_shared_index {α β : Type} {entries : List α} {map : α → List β}
    {left right : Nat} {a b : α} {value : β}
    (unique : (entries.flatMap map).Nodup)
    (leftAt : entries[left]? = some a) (rightAt : entries[right]? = some b)
    (leftMember : value ∈ map a) (rightMember : value ∈ map b) : left = right := by
  induction entries generalizing left right with
  | nil => simp at leftAt
  | cons first rest ih =>
    rw [List.flatMap_cons,List.nodup_append] at unique
    cases left with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at leftAt
      subst a
      cases right with
      | zero => rfl
      | succ right =>
        have member : value ∈ rest.flatMap map :=
          List.mem_flatMap.mpr ⟨b,List.mem_of_getElem? rightAt,rightMember⟩
        exact False.elim (unique.2.2 value leftMember value member rfl)
    | succ left =>
      cases right with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at rightAt
        subst b
        have member : value ∈ rest.flatMap map :=
          List.mem_flatMap.mpr ⟨a,List.mem_of_getElem? leftAt,leftMember⟩
        exact False.elim (unique.2.2 value rightMember value member rfl)
      | succ right => exact congrArg Nat.succ (ih unique.2.1 leftAt rightAt)

private theorem shared_child_index {parent left right : DemandNode} {leftIndex rightIndex scope : Nat}
    (unique : (sourceNodeScopeKeys parent).Nodup)
    (leftAt : parent.child? leftIndex = some left) (rightAt : parent.child? rightIndex = some right)
    (leftMember : scope ∈ sourceNodeScopeKeys left) (rightMember : scope ∈ sourceNodeScopeKeys right) :
    leftIndex = rightIndex := by
  rw [scope_keys_children,List.nodup_append] at unique
  have leftRow : parent.children[leftIndex]? = some (some left) := by
    cases found : parent.children[leftIndex]? <;> simp_all [DemandNode.child?]
  have rightRow : parent.children[rightIndex]? = some (some right) := by
    cases found : parent.children[rightIndex]? <;> simp_all [DemandNode.child?]
  exact flatMap_shared_index unique.2.1 leftRow rightRow (by simpa using leftMember) (by simpa using rightMember)

theorem scope_block_localization {root subtree : DemandNode} {subtreePath blockPath : List Nat}
    {block : Block}
    (unique : (sourceNodeScopeKeys root).Nodup)
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (blockAt : DemandNodeAt root blockPath (.block block))
    (scopeMember : block.scope ∈ sourceNodeScopeKeys subtree) : subtreePath <+: blockPath := by
  induction subtreeAt generalizing blockPath with
  | here => exact List.nil_prefix
  | @child parent child subtree index path row source ih =>
    cases blockAt with
    | here =>
      have childMember := source_keys_subset source scopeMember
      have childMember := child_keys_member row childMember
      rw [scope_keys_children,List.nodup_append] at unique
      have ownMember : block.scope ∈ ownScopeKeys (.block block) := by cases block; simp [ownScopeKeys,Block.scope]
      exact False.elim (unique.2.2 block.scope ownMember block.scope childMember rfl)
    | @child _ other _ otherIndex otherPath otherRow otherSource =>
      have childMember := source_keys_subset source scopeMember
      have otherMember : block.scope ∈ sourceNodeScopeKeys other :=
        source_keys_subset otherSource (by
          rw [scope_keys_children]
          exact List.mem_append_left _ (by cases block; simp [ownScopeKeys,Block.scope]))
      have same := shared_child_index unique row otherRow childMember otherMember
      subst otherIndex
      have same : other = child := Option.some.inj (otherRow.symm.trans row)
      subst other
      have childUnique : (sourceNodeScopeKeys child).Nodup := by
        rw [scope_keys_children,List.nodup_append] at unique
        have pairwise := List.pairwise_flatMap.mp unique.2.1
        have childRow : some child ∈ parent.children := by
          cases found : parent.children[index]? <;> simp_all [DemandNode.child?]
          exact List.mem_of_getElem? found
        exact (List.nodup_iff_pairwise_ne.mpr (by simpa using pairwise.1 (some child) childRow))
      exact List.cons_prefix_cons.mpr ⟨rfl,ih childUnique otherSource scopeMember⟩

def lexicalScopes? (node : DemandNode) : List Nat → Option (List Nat)
  | [] => some []
  | index :: path => do
    let child ← node.child? index
    let scopes ← lexicalScopes? child path
    pure (ownScopeKeys node ++ scopes)

theorem lexical_scope_enclosing_block {root node : DemandNode} {path scopes : List Nat} {scope : Nat}
    (source : DemandNodeAt root path node)
    (stackAt : lexicalScopes? root path = some scopes) (member : scope ∈ scopes) :
    ∃ block blockPath, DemandNodeAt root blockPath (.block block) ∧
      block.scope = scope ∧ blockPath <+: path := by
  induction source generalizing scopes with
  | here =>
    simp only [lexicalScopes?,Option.some.injEq] at stackAt
    subst scopes
    cases member
  | @child parent child node index path row source ih =>
    simp only [lexicalScopes?,row] at stackAt
    cases childStackAt : lexicalScopes? child path with
    | none => simp [childStackAt] at stackAt
    | some childScopes =>
      simp [childStackAt] at stackAt
      subst scopes
      rcases List.mem_append.mp member with own | inherited
      · cases parent with
        | block block =>
          have same : block.scope = scope := by
            have same : scope = block.scope := by cases block; simpa [ownScopeKeys,Block.scope] using own
            exact same.symm
          exact ⟨block,[],.here _,same,List.nil_prefix⟩
        | _ => simp [ownScopeKeys] at own
      · obtain ⟨block,blockPath,blockAt,same,earlier⟩ := ih childStackAt inherited
        exact ⟨block,index :: blockPath,.child row blockAt,same,List.cons_prefix_cons.mpr ⟨rfl,earlier⟩⟩

theorem lexical_scope_writer_localization {root subtree writer : DemandNode}
    {subtreePath writerPath scopes : List Nat} {scope : Nat}
    (unique : (sourceNodeScopeKeys root).Nodup)
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (writerAt : DemandNodeAt root writerPath writer)
    (stackAt : lexicalScopes? root writerPath = some scopes)
    (active : scope ∈ scopes) (fresh : scope ∈ sourceNodeScopeKeys subtree) :
    subtreePath <+: writerPath := by
  obtain ⟨block,blockPath,blockAt,same,earlier⟩ := lexical_scope_enclosing_block writerAt stackAt active
  have inside := scope_block_localization unique subtreeAt blockAt (same.symm ▸ fresh)
  exact inside.trans earlier


theorem writer_scope_localization {root subtree writer : DemandNode}
    {subtreePath writerPath scopes : List Nat} {scope : Nat}
    (unique : (sourceNodeScopeKeys root).Nodup)
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (writerAt : DemandNodeAt root writerPath writer)
    (stackAt : lexicalScopes? root writerPath = some scopes)
    (active : scope ∈ ownScopeKeys writer ++ scopes)
    (fresh : scope ∈ sourceNodeScopeKeys subtree) : subtreePath <+: writerPath := by
  rcases List.mem_append.mp active with own | inherited
  · cases writer with
    | block block =>
      have same : scope = block.scope := by cases block; simpa [ownScopeKeys,Block.scope] using own
      exact scope_block_localization unique subtreeAt writerAt (same ▸ fresh)
    | _ => simp [ownScopeKeys] at own
  · exact lexical_scope_writer_localization unique subtreeAt writerAt stackAt inherited fresh

theorem typed_variable_writer_localization {root subtree writer : DemandNode}
    {subtreePath writerPath scopes : List Nat} {env : TEnv} {varId : VarId}
    {localVar : LocalVar} {start finish : Nat}
    (unique : (sourceNodeScopeKeys root).Nodup)
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (writerAt : DemandNodeAt root writerPath writer)
    (stackAt : lexicalScopes? root writerPath = some scopes)
    (visible : StorageWalkVisible env scopes)
    (variableAt : Core.varOf env varId start = .ok (localVar,finish))
    (fresh : localVar.scope ∈ sourceNodeScopeKeys subtree) : subtreePath <+: writerPath :=
  lexical_scope_writer_localization unique subtreeAt writerAt stackAt
    (visible.varOf variableAt) fresh

theorem typed_declaration_writer_localization {root subtree writer : DemandNode}
    {subtreePath writerPath scopes : List Nat} {env : TEnv} {varId scope : Nat}
    {localVar : LocalVar} {start finish : Nat}
    (unique : (sourceNodeScopeKeys root).Nodup)
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (writerAt : DemandNodeAt root writerPath writer)
    (stackAt : lexicalScopes? root writerPath = some scopes)
    (active : scope ∈ scopes)
    (variableAt : Core.declare env varId scope start = .ok (localVar,finish))
    (fresh : localVar.scope ∈ sourceNodeScopeKeys subtree) : subtreePath <+: writerPath := by
  have same := (Goose.Core.Sound.declare_ok _ _ _ _ _ variableAt).2.2.1
  exact lexical_scope_writer_localization unique subtreeAt writerAt stackAt active (same ▸ fresh)

theorem source_path_suffix {root subtree writer : DemandNode} {subtreePath writerPath : List Nat}
    (subtreeAt : DemandNodeAt root subtreePath subtree)
    (writerAt : DemandNodeAt root writerPath writer) (within : subtreePath <+: writerPath) :
    ∃ suffix, writerPath = subtreePath ++ suffix ∧ DemandNodeAt subtree suffix writer := by
  induction subtreeAt generalizing writerPath with
  | here => exact ⟨writerPath,rfl,writerAt⟩
  | @child parent child subtree index path row source ih =>
    cases writerAt with
    | here => simp at within
    | @child _ other writer otherIndex otherPath otherRow otherSource =>
      obtain ⟨same,remaining⟩ := List.cons_prefix_cons.mp within
      subst otherIndex
      have same : other = child := Option.some.inj (otherRow.symm.trans row)
      subst other
      obtain ⟨suffix,same,source⟩ := ih otherSource remaining
      exact ⟨suffix,by simp [same],source⟩

#print axioms scope_block_localization
#print axioms lexical_scope_writer_localization
#print axioms writer_scope_localization
#print axioms typed_variable_writer_localization
#print axioms typed_declaration_writer_localization
#print axioms source_path_suffix

end Goose.Lower.Validation.SourceReplacementLexicalWriters
