import Goose.Lower.Validation.SourceReplacementWriterLedgerAccepted
import Goose.Lower.Validation.SourceReplacementWriterTypingIndexedAccepted

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation SourceReplacementWriterTyping

private def BindingsScoped (variables : Array LocalVar) : Fragment → Prop
  | .block _ bindings _ block => ∀ binding ∈ bindings,
      ∃ localVar, variables[binding.1]? = some localVar ∧ localVar.scope = block.scope
  | _ => True

private def ChildrenBindingsScoped (variables : Array LocalVar) : List Child → Prop
  | [] => True
  | none :: rest => ChildrenBindingsScoped variables rest
  | some (fragment, _) :: rest => BindingsScoped variables fragment ∧ ChildrenBindingsScoped variables rest

private theorem ChildrenBindingsScoped.append {variables : Array LocalVar} {left right : List Child}
    (first : ChildrenBindingsScoped variables left) (second : ChildrenBindingsScoped variables right) :
    ChildrenBindingsScoped variables (left ++ right) := by
  induction left with
  | nil => exact second
  | cons entry rest ih => cases entry <;> first | exact ih first | exact ⟨first.1, ih first.2⟩

private theorem ChildrenBindingsScoped.member {variables : Array LocalVar} {children : List Child}
    (classified : ChildrenBindingsScoped variables children) {fragment : Fragment} {before : LS}
    (member : some (fragment, before) ∈ children) : BindingsScoped variables fragment := by
  induction children with
  | nil => simp at member
  | cons entry rest ih =>
    cases entry with
    | none => exact ih classified (by simpa using member)
    | some pair =>
      rcases List.mem_cons.mp member with same | member
      · cases Option.some.inj same
        exact classified.1
      · exact ih classified.2 member

private theorem expressionChildren_scoped (variables : Array LocalVar) (env : LEnv) (expressions : List Expr) (before : LS) :
    ChildrenBindingsScoped variables (expressionChildren env expressions before) := by
  induction expressions generalizing before with
  | nil => trivial
  | cons expression rest ih => exact ⟨trivial, ih _⟩

private theorem argumentChildren_scoped (variables : Array LocalVar) (env : LEnv) (arguments : List Arg) (before : LS) :
    ChildrenBindingsScoped variables (argumentChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih => cases argument <;> exact ⟨trivial, ih _⟩

private theorem printChildren_scoped (variables : Array LocalVar) (env : LEnv) (arguments : List PrintArg) (before : LS) :
    ChildrenBindingsScoped variables (printChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih => cases argument <;> first | exact ih _ | exact ⟨trivial, ih _⟩

private theorem statementChildren_scoped (variables : Array LocalVar) (env : LEnv) (loop : Option LoopCtx)
    (statements : List Stmt) (before : LS) : ChildrenBindingsScoped variables (statementChildren env loop statements before) := by
  induction statements generalizing before with
  | nil => trivial
  | cons statement rest ih => simp only [statementChildren]; split <;> first | exact ih _ | exact ⟨trivial, ih _⟩

private theorem branchChildren_scoped (variables : Array LocalVar) (env : LEnv) (before : LS) (condition : ValueId)
    (loop : Option LoopCtx) (want : Bool) (yes : Core.Block) (no : Option Core.Block) :
    ChildrenBindingsScoped variables (branchChildren env before condition loop want yes no) := by
  unfold branchChildren
  split <;> cases no <;> simp [ChildrenBindingsScoped, BindingsScoped]

private theorem shortCircuitChild_scoped (variables : Array LocalVar) (env : LEnv) (before : LS)
    (isAnd : Bool) (left : ValueId) (right : Expr) :
    ChildrenBindingsScoped variables [shortCircuitChild env before isAnd left right] := by
  unfold shortCircuitChild
  split <;> trivial

private theorem whileChildren_scoped (variables : Array LocalVar) (env : LEnv) (before : LS) (condition : Expr) (body : Core.Block) :
    ChildrenBindingsScoped variables (whileChildren env before condition body) := by
  unfold whileChildren
  dsimp only
  refine ⟨trivial, ?_⟩
  split <;> simp [ChildrenBindingsScoped, BindingsScoped]

private theorem rangeChild_scoped {sourceEnv output : TEnv} {scope start finish varId : Nat}
    {low high : Expr} {body : Core.Block} {origin : OriginId}
    (typed : tyStmt sourceEnv scope (.forRange varId low high body origin) start = .ok (output, finish))
    (env : LEnv) (before : LS) (first last : ValueId) :
    ChildrenBindingsScoped sourceEnv.vars [rangeChild env before varId first last body origin] := by
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType, declared, _⟩ := tyStmt_forRange_children typed
  have declaration := declare_ok _ _ _ _ _ declared
  unfold rangeChild
  split
  · refine ⟨?_, trivial⟩
    intro binding member
    have same := List.mem_singleton.mp member
    subst binding
    exact ⟨localVar, declaration.2.1, declaration.2.2.1⟩
  · trivial

private theorem eachChild_scoped {sourceEnv output : TEnv} {scope start finish varId : Nat}
    {iterationIndex : Option VarId} {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    (typed : tyStmt sourceEnv scope (.forEach varId iterationIndex view byRef body origin) start = .ok (output, finish))
    (env : LEnv) (before : LS) :
    ChildrenBindingsScoped sourceEnv.vars [eachChild env before varId iterationIndex view byRef body origin] := by
  obtain ⟨_, localVar, variableAt, variableScope, indexFacts⟩ := tyStmt_forEach_bindings typed
  unfold eachChild
  dsimp only
  split
  · refine ⟨?_, trivial⟩
    intro binding member
    rcases List.mem_cons.mp member with same | member
    · subst binding
      exact ⟨localVar, variableAt, variableScope⟩
    · obtain ⟨i, inIndex, same⟩ := List.mem_map.mp member
      subst binding
      have selected : iterationIndex = some i := by simpa only [Option.mem_toList] using inIndex
      obtain ⟨_, indexVar, row, scopeEq, _⟩ := indexFacts i selected
      exact ⟨indexVar, row, scopeEq⟩
  · trivial

private theorem Fragment.children_bindings_scoped {sourceEnv : TEnv} (fragment : Fragment)
    (typed : NodeTyped sourceEnv fragment.node) (env : LEnv) (before : LS) :
    ChildrenBindingsScoped sourceEnv.vars (fragment.children env before) := by
  cases fragment with
  | expression expression =>
    cases expression <;> try trivial
    case and left right => exact ⟨trivial, shortCircuitChild_scoped _ _ _ _ _ _⟩
    case or left right => exact ⟨trivial, shortCircuitChild_scoped _ _ _ _ _ _⟩
    case call function arguments origin => exact argumentChildren_scoped _ _ _ _
    case ifE condition yes no => exact ⟨trivial, branchChildren_scoped _ _ _ _ _ _ _ _⟩
    case blockE block => simp [Fragment.children, ChildrenBindingsScoped, BindingsScoped]
    case arrLit type expressions => exact expressionChildren_scoped _ _ _ _
    case structLit type expressions => exact expressionChildren_scoped _ _ _ _
  | place place => cases place <;> trivial
  | view view => cases view <;> trivial
  | bound bound => cases bound <;> trivial
  | statement loop statement =>
    cases statement <;> try trivial
    case resize place size fill origin => cases fill <;> trivial
    case ifS condition yes no origin => exact ⟨trivial, branchChildren_scoped _ _ _ _ _ _ _ _⟩
    case «while» condition body origin => exact whileChildren_scoped _ _ _ _ _
    case forRange varId low high body origin =>
      cases typed with
      | statement active source => exact ⟨trivial, trivial, rangeChild_scoped source _ _ _ _⟩
    case forEach varId iterationIndex view byRef body origin =>
      cases typed with
      | statement active source => exact ⟨trivial, eachChild_scoped source _ _⟩
    case ret expression origin => cases expression <;> trivial
    case print arguments origin => exact printChildren_scoped _ _ _ _
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      apply ChildrenBindingsScoped.append
      · exact statementChildren_scoped _ _ _ _ _
      · cases value <;> trivial

private theorem scoped_at_path {root fragment : Fragment} {sourceEnv : TEnv} {env : LEnv}
    {initial before : LS} {path : List Nat}
    (typed : NodeTyped sourceEnv root.node) (rootBindings : BindingsScoped sourceEnv.vars root)
    (located : SourceLoweringAt root env initial path fragment before) :
    BindingsScoped sourceEnv.vars fragment := by
  induction path generalizing root initial sourceEnv with
  | nil =>
    have same : (root, initial) = (fragment, before) := Option.some.inj located
    cases same
    exact rootBindings
  | cons index rest ih =>
    unfold SourceLoweringAt Fragment.at? at located
    cases found : root.child? env initial index with
    | none => simp [found] at located
    | some pair =>
      obtain ⟨child, start⟩ := pair
      simp only [found] at located
      have childScoped := (root.children_bindings_scoped typed env initial).member (Fragment.child_member found)
      obtain ⟨after, context, childTyped⟩ := typed.indexed_child (Fragment.child_source found)
      have actualScoped : BindingsScoped after.vars child := by simpa only [context.varsEq] using childScoped
      have result := ih childTyped actualScoped located
      simpa only [context.varsEq] using result

theorem contextEntryBindings_scope {module : Core.Module} {impl : Impl} {implId : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implId]? = some impl)
    (env : LEnv) {binding : SlotId × ValueId × OriginId} (member : binding ∈ contextEntryBindings impl env) :
    ∃ localVar, impl.vars[binding.1]? = some localVar ∧ localVar.scope = impl.body.scope := by
  obtain ⟨⟨parameter, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, _, parameterAt, aligned, _⟩ := entry_parameter_pair env accepted implAt paired
  have checked := (validate_modOk module accepted).impl _ _ implAt
  obtain ⟨_, localVar, row, scopeEq, _⟩ := checked.params index parameter parameterAt
  exact ⟨localVar, by simpa only [aligned] using row, scopeEq.trans checked.bodyScope.symm⟩

theorem context_block_prebinding_scope {module : Core.Module} {impl : Impl} {implId : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implId]? = some impl)
    {path : List Nat} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)}
    {want : Bool} {body : Core.Block} {before : LS}
    (located : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) path (.block loop bindings want body) before)
    {binding : SlotId × ValueId × OriginId} (member : binding ∈ bindings) :
    ∃ localVar, impl.vars[binding.1]? = some localVar ∧ localVar.scope = body.scope := by
  have checked := (validate_modOk module accepted).impl _ _ implAt
  obtain ⟨type, finish, typed, _⟩ := checked.body
  have initialTyped : NodeTyped (implEnv module impl) (contextFragment module impl).node := .block typed
  have initialScoped : BindingsScoped (implEnv module impl).vars (contextFragment module impl) := by
    intro binding member
    exact contextEntryBindings_scope accepted implAt _ member
  exact scoped_at_path initialTyped initialScoped located binding member

theorem context_block_prebinding_scope_of_row {module : Core.Module} {impl : Impl} {implId : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implId]? = some impl)
    {path : List Nat} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)}
    {want : Bool} {body : Core.Block} {before : LS}
    (located : SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) path (.block loop bindings want body) before)
    {binding : SlotId × ValueId × OriginId} (member : binding ∈ bindings)
    {localVar : LocalVar} (row : impl.vars[binding.1]? = some localVar) : localVar.scope = body.scope := by
  obtain ⟨actual, actualAt, scopeEq⟩ := context_block_prebinding_scope accepted implAt located member
  have same : actual = localVar := Option.some.inj (actualAt.symm.trans row)
  exact same ▸ scopeEq

#print axioms contextEntryBindings_scope
#print axioms context_block_prebinding_scope
#print axioms context_block_prebinding_scope_of_row

end Goose.Lower.Validation.SourceReplacementWriterLedger
