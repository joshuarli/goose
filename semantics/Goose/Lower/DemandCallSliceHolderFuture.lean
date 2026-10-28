import Goose.Lower.DemandCallSliceSlot

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem callArgsFuture_priorSliceHolder {m : Core.Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {tenv : TEnv} {penv : PEnv} {env : Env}
    (context : EvaluationContext m plans path (.expression (.call contextId arguments origin)) .expression)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (variables : tenv.vars = env.vars) {slot : VarId} {lv : LocalVar}
    {mutability : Mutability} {element : Ty} (variableAt : env.vars[slot]? = some lv)
    (variableType : lv.ty = .slice mutability element) (visible : slot ∈ tenv.visible)
    {index offset : Nat} {borrow : Mutability}
    (found : arguments[index]? = some (.byRef borrow (.var slot))) (prior : index < offset) :
    slot ∈ callArgsFuture context offset (arguments.drop offset) := by
  cases context with
  | pilot profile activeVariables =>
    simp only [callArgsFuture, List.mem_append]
    exact Or.inr ((active slot).2 visible)
  | @shrink pc profile context =>
    have accessVariable : pc.approvals.access.impl.vars[slot]? = some lv := by
      rw [access.2.1, variables]
      exact variableAt
    have lookup : pc.approvals.access.placeType? (.var slot) = some (.slice mutability element) := by
      simp [AccessEnv.placeType?, accessVariable, variableType]
    have member : .byRef borrow (.var slot) ∈ arguments.take offset := by
      have atIndex : (arguments.take offset)[index]? = some (.byRef borrow (.var slot)) := by
        simpa [List.getElem?_take, prior] using found
      exact List.mem_of_getElem? atIndex
    simp only [callArgsFuture, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨.byRef borrow (.var slot), member, by simp [Arg.sliceHolderVariables, lookup, Place.variables]⟩)

theorem callArgContext_priorSliceHolder {m : Core.Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {tenv : TEnv} {penv : PEnv} {env : Env}
    (context : EvaluationContext m plans path (.expression (.call contextId arguments origin)) .expression)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (variables : tenv.vars = env.vars) {slot : VarId} {lv : LocalVar}
    {mutability : Mutability} {element : Ty} (variableAt : env.vars[slot]? = some lv)
    (variableType : lv.ty = .slice mutability element) (visible : slot ∈ tenv.visible)
    {index priorIndex : Nat} {borrow : Mutability} {argument : Arg}
    (current : arguments[index]? = some argument)
    (found : arguments[priorIndex]? = some (.byRef borrow (.var slot))) (prior : priorIndex < index) :
    slot ∈ (callArgContext context index argument current).inputFuture := by
  rw [callArgContext_input_output]
  apply List.mem_append_right
  cases context with
  | pilot profile activeVariables =>
    cases argument <;> simp [callArgContext, ArgContext.outputFuture, EvaluationContext.child,
      EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild, (active slot).2 visible]
  | @shrink pc profile context =>
    rw [callArgContext_shrinkOutputFuture context profile index argument (arguments.drop (index + 1)) current rfl]
    exact callArgsFuture_priorSliceHolder (.shrink profile context) active access variables variableAt variableType visible found (by omega)

theorem demandContextInputFutureEq {module : Core.Module}
    {firstPlans secondPlans : Array (Array DemandPoint)} {firstPath secondPath : List Nat}
    {firstNode secondNode : DemandNode} {phase : DemandPhase}
    {first : EvaluationContext module firstPlans firstPath firstNode phase}
    {second : EvaluationContext module secondPlans secondPath secondNode phase}
    (plans : firstPlans = secondPlans) (path : firstPath = secondPath) (node : firstNode = secondNode)
    (same : HEq first second) : first.inputFuture = second.inputFuture := by
  subst secondPlans
  subst secondPath
  subst secondNode
  exact congrArg EvaluationContext.inputFuture (eq_of_heq same)

theorem SliceSlotAliasAt.ofLaterValueArgument {cfg : Cfg} {env : Env} {initial state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {index priorIndex : Nat} {expression : Expr} {borrow : Mutability} {slot : VarId}
    (current : arguments[index]? = some (.byVal expression))
    (found : arguments[priorIndex]? = some (.byRef borrow (.var slot))) (prior : priorIndex < index)
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byVal expression) current))
    {si : ScopeInst} {lv : LocalVar} {mutability : Mutability} {element : Ty}
    {frame : GIR.Frame} {id : ValueId} {alias : RetainedAlias}
    (visible : slot ∈ root.typingEnv.visible) (variableAt : env.vars[slot]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si) (variableType : lv.ty = .slice mutability element)
    (annotation : root.rootsEnv.ann slot = some alias.roots) (aliasType : alias.ty = .slice mutability element)
    (cell : frame.vals[id]? = some (.val (.ref ⟨.local env.act si slot, []⟩))) :
    SliceSlotAliasAt cfg.mod root.world env state.store frame id alias mutability element := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have contextEq : HEq child.context
      (root.context.child rfl index (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, current]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using childContext
  have futureEq := demandContextInputFutureEq plans path rfl contextEq
  have needed := callArgContext_priorSliceHolder root.context root.active root.access root.frame.vars_t
    variableAt variableType visible current found prior
  have childNeeded : slot ∈ child.context.inputFuture := by
    rw [futureEq]
    simpa only [callArgContext, ArgContext.inputFuture] using needed
  have childVisible : slot ∈ child.typingEnv.visible := by simpa only [typing] using visible
  have childAnnotation : child.rootsEnv.ann slot = some alias.roots := by simpa only [roots] using annotation
  have result := SliceSlotAliasAt.ofFrame child.frame childVisible childNeeded variableAt scope variableType childAnnotation aliasType cell
  simpa only [world] using result


theorem SliceSlotAliasAt.ofLaterReferenceArgument {cfg : Cfg} {env : Env} {initial state : St}
    {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call contextId arguments origin) initial)
    {index priorIndex : Nat} {place : Place} {borrow currentBorrow : Mutability} {slot : VarId}
    (current : arguments[index]? = some (.byRef currentBorrow place))
    (found : arguments[priorIndex]? = some (.byRef borrow (.var slot))) (prior : priorIndex < index)
    (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ place.sliceArg = true))
    (canonical : (ArgSource.byRef currentBorrow child target).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byRef currentBorrow place) current))
    {si : ScopeInst} {lv : LocalVar} {mutability : Mutability} {element : Ty}
    {frame : GIR.Frame} {id : ValueId} {alias : RetainedAlias}
    (visible : slot ∈ root.typingEnv.visible) (variableAt : env.vars[slot]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si) (variableType : lv.ty = .slice mutability element)
    (annotation : root.rootsEnv.ann slot = some alias.roots) (aliasType : alias.ty = .slice mutability element)
    (cell : frame.vals[id]? = some (.val (.ref ⟨.local env.act si slot, []⟩))) :
    SliceSlotAliasAt cfg.mod root.world env state.store frame id alias mutability element := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have contextEq : HEq child.context
      (root.context.child rfl index (.place place) .place
        (by simp [DemandNode.child?, DemandNode.children, current]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using childContext
  have futureEq := demandContextInputFutureEq plans path rfl contextEq
  have needed := callArgContext_priorSliceHolder root.context root.active root.access root.frame.vars_t
    variableAt variableType visible current found prior
  have childNeeded : slot ∈ child.context.inputFuture := by
    rw [futureEq]
    simpa only [callArgContext, ArgContext.inputFuture] using needed
  have childVisible : slot ∈ child.typingEnv.visible := by simpa only [typing] using visible
  have childAnnotation : child.rootsEnv.ann slot = some alias.roots := by simpa only [roots] using annotation
  have result := SliceSlotAliasAt.ofFrame child.frame childVisible childNeeded variableAt scope variableType childAnnotation aliasType cell
  simpa only [world] using result

#print axioms demandContextInputFutureEq
#print axioms SliceSlotAliasAt.ofLaterValueArgument
#print axioms SliceSlotAliasAt.ofLaterReferenceArgument

#print axioms callArgContext_priorSliceHolder

theorem SliceSlotAliasAt.ofPriorArgumentFrame {cfg : Cfg} {plans : Array (Array DemandPoint)}
    {path : List Nat} {contextId : ContextId} {arguments : List Arg} {origin : OriginId}
    {tenv : TEnv} {penv : PEnv} {env : Env} {world : World} {state : St} {frame : GIR.Frame} {id : ValueId}
    {alias : RetainedAlias} {slot : VarId} {si : ScopeInst} {lv : LocalVar} {mutability : Mutability} {element : Ty}
    {index offset : Nat} {borrow : Mutability}
    (context : EvaluationContext cfg.mod plans path (.expression (.call contextId arguments origin)) .expression)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (source : Core.Sound.Frame cfg.mod world tenv penv env state (callArgsFuture context offset (arguments.drop offset)))
    (visible : slot ∈ tenv.visible) (variableAt : env.vars[slot]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si) (variableType : lv.ty = .slice mutability element)
    (annotation : penv.ann slot = some alias.roots) (aliasType : alias.ty = .slice mutability element)
    (cell : frame.vals[id]? = some (.val (.ref ⟨.local env.act si slot, []⟩)))
    (found : arguments[index]? = some (.byRef borrow (.var slot))) (prior : index < offset) :
    SliceSlotAliasAt cfg.mod world env state.store frame id alias mutability element := by
  have needed := callArgsFuture_priorSliceHolder context active access source.vars_t variableAt variableType visible found prior
  exact SliceSlotAliasAt.ofFrame source visible needed variableAt scope variableType annotation aliasType cell

#print axioms SliceSlotAliasAt.ofPriorArgumentFrame

#print axioms callArgsFuture_priorSliceHolder
end Goose.Lower
