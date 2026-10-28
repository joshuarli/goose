import Goose.Lower.DemandGeneratedRows
import Goose.Lower.DemandGeneratedTransfer
import Goose.Lower.ReflectionSources

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem GeneratedCallArgumentRows.length {access : AccessEnv} {path : List Nat}
    {index : Nat} {arguments : List Arg} {ids : List ValueId} {retained : List (ValueId × RetainedAlias)}
    (rows : GeneratedCallArgumentRows access path index arguments ids retained) : arguments.length = ids.length := by
  induction rows with
  | nil => rfl
  | cons query tail ih => simp [ih]

theorem GeneratedCallArgumentRows.lookup {access : AccessEnv} {path : List Nat}
    {index : Nat} {arguments : List Arg} {ids : List ValueId} {retained : List (ValueId × RetainedAlias)}
    (rows : GeneratedCallArgumentRows access path index arguments ids retained)
    {position : Nat} {argument : Arg} {id : ValueId}
    (argumentAt : arguments[position]? = some argument) (idAt : ids[position]? = some id) :
    ∃ aliases, access.aliasArg (path ++ [index + position]) argument = .ok aliases ∧
      ∀ alias, alias ∈ aliases → (id, alias) ∈ retained := by
  induction rows generalizing position with
  | nil => simp at argumentAt
  | @cons index head rest value ids aliases retained query tail ih =>
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at argumentAt idAt
      subst argument
      subst id
      refine ⟨aliases, by simpa using query, ?_⟩
      intro alias member
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨alias, member, rfl⟩
    | succ position =>
      simp only [List.getElem?_cons_succ] at argumentAt idAt
      obtain ⟨aliases, query, present⟩ := ih argumentAt idAt
      refine ⟨aliases, ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm 1 position, Nat.add_left_comm] using query
      · intro alias member
        exact List.mem_append_right _ (present alias member)

theorem ArgSource.byVal_callChild {cfg : Cfg} {env : Env} {initial state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initial)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world (callArgContext root.context index (.byVal expression) found)) :
    root.ChildAt child index (by simp [DemandNode.child?, DemandNode.children, found]) := by
  obtain ⟨plans, path, world, context⟩ := canonical
  have childContext : HEq child.context
      (root.context.child rfl index (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, found]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using context
  refine ⟨world, path, plans, childContext, ?_⟩
  intro alias member
  have retained := callArgContext_retained_subset root.context index (.byVal expression) found member
  have eq := demandContextRetainedEq plans path rfl childContext
  simpa only [callArgContext, ArgContext.retained, eq] using retained

theorem ArgsSource.atFuel_callChildren {n k : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {context : ContextId} {all : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context all origin) initial)
    {arguments : List Arg} {state : St} (bound : n ≤ k) (source : ArgsSource k cfg env arguments state)
    {offset : Nat} (canonical : source.CallChildren root offset) :
    (source.atFuel bound).CallChildren root offset := by
  induction arguments generalizing state offset with
  | nil => cases source; trivial
  | cons argument rest ih =>
    cases source with
    | cons head tail =>
      obtain ⟨found, headCanonical, tailCanonical⟩ := canonical
      refine ⟨found, headCanonical, ?_⟩
      intro value after done
      exact ih _ (tailCanonical value after (((Goose.Proofs.Fuel.monoAll n k bound).arg cfg env argument state).1 value after done))

theorem ArgsSource.afterHead_callChildren {n : Nat} {cfg : Cfg} {env : Env} {initial state after : St}
    {context : ContextId} {all : List Arg} {origin : OriginId} {argument : Arg} {rest : List Arg}
    (root : ExprSource cfg env (.call context all origin) initial)
    (sources : ∀ fuel, ArgsSource fuel cfg env (argument :: rest) state) {offset : Nat}
    (canonical : ∀ fuel, (sources fuel).CallChildren root offset)
    {value : Val} (done : evalArg n cfg env argument state = .ok value after) (fuel : Nat) :
    (ArgsSource.afterHead sources done fuel).CallChildren root (offset + 1) := by
  cases sourceEq : sources (max n fuel) with
  | cons head tail =>
    have evidence := canonical (max n fuel)
    rw [sourceEq] at evidence
    obtain ⟨found, headCanonical, tailCanonical⟩ := evidence
    have next := tailCanonical value after
      (((Goose.Proofs.Fuel.monoAll n (max n fuel) (Nat.le_max_left _ _)).arg cfg env argument state).1 value after done)
    change (((sources (max n fuel)).tail _).atFuel (Nat.le_max_right _ _)).CallChildren root (offset + 1)
    rw [sourceEq]
    exact ArgsSource.atFuel_callChildren root (Nat.le_max_right _ _) _ next

#print axioms GeneratedCallArgumentRows.length
#print axioms GeneratedCallArgumentRows.lookup
#print axioms ExprSource.callArgsCanonical
#print axioms ArgSource.byVal_callChild
#print axioms ArgsSource.atFuel_callChildren
#print axioms ArgsSource.afterHead_callChildren
end Goose.Lower
