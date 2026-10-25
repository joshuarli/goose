import Goose.Lower.Validation.SourceReplacementCallContentsApartAliases

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem add_binders_preserves (binders visible : List VarId) :
    visible ⊆ binders.foldl (fun active binder => if active.contains binder then active else binder :: active) visible := by
  apply List.foldlRecOn (motive := fun active : List VarId => visible ⊆ active) binders _ (List.Subset.refl _)
  intro active bounded binder member varId visibleAt
  split
  · exact bounded visibleAt
  · exact List.mem_cons_of_mem binder (bounded visibleAt)

theorem DemandNode.visibleForChild_preserves (node : DemandNode) (visible : List VarId) (index : Nat) :
    visible ⊆ node.visibleForChild visible index := by
  cases node with
  | block body =>
    cases body with
    | mk scope statements value =>
      simp only [DemandNode.visibleForChild]
      apply List.foldlRecOn (motive := fun active : List VarId => visible ⊆ active)
        (statements.take index) _ (List.Subset.refl _)
      intro active bounded statement member varId visibleAt
      cases statement <;> dsimp only <;> try exact bounded visibleAt
      case letS binder expression origin =>
        split
        · exact bounded visibleAt
        · exact List.mem_cons_of_mem binder (bounded visibleAt)
  | statement statement =>
    cases statement <;> try exact List.Subset.refl _
    case forRange binder lo hi body origin =>
      simp only [DemandNode.visibleForChild]
      split
      · exact fun varId member => List.mem_cons_of_mem _ member
      · exact List.Subset.refl _
    case forEach binder indexed view reference body origin =>
      simp only [DemandNode.visibleForChild]
      split
      · exact add_binders_preserves (binder :: indexed.toList) visible
      · exact List.Subset.refl _
  | _ => exact List.Subset.refl _

theorem _root_.Goose.Core.Sound.NodeContext.active_matches {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (left right : NodeContext pc path node phase) :
    ∀ varId, varId ∈ left.expected.frame.active ↔ varId ∈ right.expected.frame.active := by
  have same := Option.some.inj (left.focus.focus.lookup.symm.trans right.focus.focus.lookup)
  intro varId
  exact (left.focus.frameMatches.1 varId).symm.trans
    (same ▸ right.focus.frameMatches.1 varId)

private theorem descendant_active {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {parent node : DemandNode} {suffix : List Nat}
    (source : DemandNodeAt parent suffix node) :
    ∀ {front} (context : NodeContext pc front parent parent.primaryPhase),
      ∃ descendant : NodeContext pc (front ++ suffix) node node.primaryPhase,
        context.expected.frame.active ⊆ descendant.expected.frame.active := by
  induction source with
  | here parent =>
      intro front context
      rw [List.append_nil]
      exact ⟨context, List.Subset.refl _⟩
  | @child parent middle node index suffix row source ih =>
      intro front context
      have phase : DemandNodeHasPhase middle middle.primaryPhase := by
        cases middle <;> simp [DemandNodeHasPhase, DemandNode.primaryPhase, DemandNode.phaseMatches]
      let transition := context.child rfl index middle middle.primaryPhase row phase
      have active : context.expected.frame.active ⊆ transition.context.expected.frame.active := by
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_active transition.phaseFrameEq,
          DemandNode.childFrame_active transition.childFrameEq]
        exact DemandNode.visibleForChild_preserves parent context.expected.frame.active index
      obtain ⟨descendant, inherited⟩ := ih transition.context
      have pathEq : front ++ index :: suffix = (front ++ [index]) ++ suffix := by simp [List.append_assoc]
      rw [pathEq]
      exact ⟨descendant, active.trans inherited⟩

theorem _root_.Goose.Core.Sound.NodeContext.initial_active {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {path : List Nat} {node : DemandNode}
    (context : NodeContext pc path node node.primaryPhase) :
    demandInitialActive module pc.owner ⊆ context.expected.frame.active := by
  obtain ⟨root, rootAt, source⟩ := context.focus.focus.sourceAt
  let initial := NodeContext.atRoot pc root rootAt
  obtain ⟨descendant, included⟩ := descendant_active source initial
  have initialActive : initial.expected.frame.active = demandInitialActive module pc.owner :=
    NodeContext.atRoot_active pc root rootAt
  simp only [List.nil_append] at descendant included
  intro varId member
  have inherited := included (initialActive ▸ member)
  exact (descendant.active_matches context varId).mp inherited

theorem ReplacementDemandContext.parameter_active {module : Core.Module}
    {contextIndex : ContextId} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    {context : Context} {implementation : Impl}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {index : Nat} {parameter : Param} (parameterAt : implementation.params[index]? = some parameter) :
    parameter.var ∈ demand.statement.expected.frame.active := by
  apply demand.statement.initial_active
  rw [demand.owner_eq]
  have bound := (Array.getElem?_eq_some_iff.mp contextAt).1
  simp only [demandInitialActive, bound, ↓reduceIte, contextAt, implementationAt]
  exact List.mem_map.mpr ⟨parameter, Array.mem_toList_iff.mpr (Array.mem_of_getElem? parameterAt), rfl⟩

theorem DemandNode.child_variables {parent child : DemandNode} {index : Nat}
    (row : parent.child? index = some child) : child.variables ⊆ parent.variables := by
  have member : some child ∈ parent.children := by
    cases selected : parent.children[index]? with
    | none => simp [DemandNode.child?, selected] at row
    | some entry =>
      cases entry with
      | none => simp [DemandNode.child?, selected] at row
      | some found =>
        have same : found = child := by simpa [DemandNode.child?, selected] using row
        subst found
        exact List.mem_of_getElem? selected
  intro varId used
  cases parent with
  | expression expression =>
    cases expression <;>
      simp_all [DemandNode.children, DemandNode.variables, Expr.variables,
        List.mem_flatMap, List.mem_map] <;> grind [DemandNode.variables, Expr.variables, Arg.variables, Stmt.variables, PrintArg.variables, Block.variables]
  | place place =>
    cases place <;> simp_all [DemandNode.children, DemandNode.variables, Place.variables] <;> grind [DemandNode.variables]
  | view view =>
    cases view <;> simp_all [DemandNode.children, DemandNode.variables, View.variables] <;> grind [DemandNode.variables]
  | bound bound =>
    cases bound <;> simp_all [DemandNode.children, DemandNode.variables, Bound.variables] <;> grind [DemandNode.variables]
  | statement statement =>
    cases statement with
    | resize owner size fill origin =>
      cases fill <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;>
        grind [DemandNode.variables]
    | ifS condition yes no origin =>
      cases no <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;>
        grind [DemandNode.variables]
    | ret value origin =>
      cases value <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables]
    | _ =>
      simp_all [DemandNode.children, DemandNode.variables, Stmt.variables,
        List.mem_flatMap, List.mem_map] <;> grind [DemandNode.variables, PrintArg.variables]
  | block body =>
    cases body with
    | mk scope statements value =>
      cases value <;> simp_all [DemandNode.children, DemandNode.variables, Block.variables,
        List.mem_flatMap, List.mem_map] <;> grind [DemandNode.variables]

theorem _root_.Goose.Core.DemandNodeAt.variables_subset {parent child : DemandNode} {path : List Nat}
    (source : DemandNodeAt parent path child) : child.variables ⊆ parent.variables := by
  induction source with
  | here node => exact List.Subset.refl _
  | child row source ih => exact ih.trans (Goose.Lower.Validation.DemandNode.child_variables row)

theorem call_argument_variable_in_rhs {rhs : Expr} {path : List Nat} {callee : ContextId}
    {arguments : List Arg} {origin : OriginId}
    (source : DemandNodeAt (.expression rhs) path (.expression (.call callee arguments origin)))
    {index : Nat} {argument : Arg} (argumentAt : arguments[index]? = some argument)
    {varId : VarId} (used : varId ∈ argument.variables) : varId ∈ rhs.variables := by
  apply source.variables_subset
  simpa only [DemandNode.variables, Expr.variables] using
    (List.mem_flatMap.mpr ⟨argument, List.mem_of_getElem? argumentAt, used⟩ : varId ∈ arguments.flatMap Arg.variables)

theorem ReplacementDemandContext.forwarded_content_alias {module : Core.Module}
    {contextIndex : ContextId} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {context : Context} {implementation : Impl}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {varId : VarId} {ceiling : List RootRef}
    (contentsAt : (context.contentRoots.find? (·.1 == varId)).map (·.2) = some ceiling) :
    varId ∈ demand.statement.expected.frame.active ∧
      ∃ alias, demand.planContext.approvals.access.aliasVariable varId = .ok (some alias) ∧
        alias.roots = ceiling ∧ alias.ty.interiorTarget?.isSome = true := by
  obtain ⟨foundImpl, implAt, checked⟩ := (validate_modOk module accepted).ctx contextIndex context contextAt
  rw [implementationAt] at implAt
  cases Option.some.inj implAt
  have reference := AdmittedSourceCalls.contentShape_reference checked.contentShape contentsAt
  have bound : varId < implementation.params.size := by
    cases found : context.contentRoots.find? (·.1 == varId) with
    | none => simp [found] at contentsAt
    | some entry =>
      have selected : entry.1 = varId := by simpa using List.find?_some found
      have row := (forAll_ok _ _).mp checked.contentShape entry (List.mem_of_find?_eq_some found)
      by_cases outside : varId < implementation.params.size
      · exact outside
      · simp [selected, outside, reject, bind, Except.bind] at row
  let parameter := implementation.params[varId]
  have parameterAt : implementation.params[varId]? = some parameter := by simp [parameter, bound]
  have aligned := ((validate_modOk module accepted).impl context.impl implementation implementationAt
    |>.params varId parameter parameterAt).1
  have active : varId ∈ demand.statement.expected.frame.active := by
    simpa only [aligned] using demand.parameter_active contextAt implementationAt parameterAt
  refine ⟨active, ?_⟩
  cases variableAt : implementation.vars[varId]? with
  | none => simp [variableAt] at reference
  | some localVar =>
    have sliceReference : localVar.ty.isRefSlice = true := by simpa [variableAt] using reference
    cases typeAt : localVar.ty <;> simp [Ty.isRefSlice, typeAt] at sliceReference
    case ref mutability payload =>
      cases payload <;> simp at sliceReference
      case slice inner element =>
        let alias : RetainedAlias := ⟨.slice inner element, ceiling, AliasSource.variable varId⟩
        refine ⟨alias, ?_, rfl, rfl⟩
        rw [demand.access_context contextAt implementationAt]
        simp [AccessEnv.aliasVariable, variableAt, typeAt, Ty.isRefSlice, sliceReference,
          AccessEnv.contentRoots, contentsAt, alias, pure, Except.pure, bind, Except.bind]

theorem ReplacementDemandContext.rhs_forwarded_content_atoms_apart {module : Core.Module}
    {contextIndex : ContextId} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {context : Context} {implementation : Impl}
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {varId : VarId} {ceiling : List RootRef}
    (contentsAt : (context.contentRoots.find? (·.1 == varId)).map (·.2) = some ceiling)
    (used : varId ∈ rhs.variables)
    {target : DemandOwner}
    (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (invalidates : target.invalidates = true)
    {func : GIR.Func} {queries : ReplacementQueries} {owner : GIR.ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner)
      (target.roots.flatMap func.expandParameterRoot))
    {state : GIR.ReplacementContentFlow.Model.State} {address : GIR.ReplacementContentFlow.Model.Roots}
    {actual : List RootRef}
    (known : GIR.ReplacementContentFlow.Model.normalize func
      (GIR.ReplacementContentFlow.Model.content func state address) = some actual)
    (within : actual ⊆ ceiling.flatMap func.expandParameterRoot) :
    (GIR.ReplacementContentFlow.Model.content func state address).AtomsWithin
      (OwnerDependencyApart (lower module) func queries owner) := by
  obtain ⟨active, alias, aliasAt, roots, interior⟩ :=
    demand.forwarded_content_alias accepted contextAt implementationAt contentsAt
  apply demand.rhs_alias_content_atoms_apart used active targetAt invalidates aliasAt interior
    closed ownerKnown known
  simpa only [roots] using within

#print axioms DemandNode.visibleForChild_preserves
#print axioms Goose.Core.Sound.NodeContext.active_matches
#print axioms Goose.Core.Sound.NodeContext.initial_active
#print axioms ReplacementDemandContext.parameter_active
#print axioms DemandNode.child_variables
#print axioms Goose.Core.DemandNodeAt.variables_subset
#print axioms call_argument_variable_in_rhs
#print axioms ReplacementDemandContext.forwarded_content_alias
#print axioms ReplacementDemandContext.rhs_forwarded_content_atoms_apart

end Goose.Lower.Validation
