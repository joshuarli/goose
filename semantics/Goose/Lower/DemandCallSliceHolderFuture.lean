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

#print axioms callArgsFuture_priorSliceHolder
end Goose.Lower
