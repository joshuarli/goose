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

theorem GeneratedCallArgumentRows.member_origin {access : AccessEnv} {path : List Nat}
    {index : Nat} {arguments : List Arg} {ids : List ValueId} {retained : List (ValueId × RetainedAlias)}
    (rows : GeneratedCallArgumentRows access path index arguments ids retained)
    {id : ValueId} {alias : RetainedAlias} (member : (id, alias) ∈ retained) :
    ∃ position argument aliases, arguments[position]? = some argument ∧ ids[position]? = some id ∧
      access.aliasArg (path ++ [index + position]) argument = .ok aliases ∧ alias ∈ aliases := by
  induction rows with
  | nil => simp at member
  | @cons index head rest value ids aliases retained query tail ih =>
    rcases List.mem_append.mp member with current | later
    · obtain ⟨a, present, equal⟩ := List.mem_map.mp current
      have pairEq : value = id ∧ a = alias := Prod.mk.inj equal
      obtain ⟨rfl, rfl⟩ := pairEq
      exact ⟨0, head, aliases, by simp, by simp, by simpa using query, present⟩
    · obtain ⟨position, argument, aliases, argumentAt, idAt, aliasQuery, present⟩ := ih later
      refine ⟨Nat.succ position, argument, aliases, ?_, ?_, ?_, present⟩
      · simpa only [List.getElem?_cons_succ] using argumentAt
      · simpa only [List.getElem?_cons_succ] using idAt
      · simpa only [Nat.add_assoc, Nat.add_comm 1 position, Nat.add_left_comm] using aliasQuery

theorem GeneratedCallArgumentRows.snoc {access : AccessEnv} {path : List Nat}
    {index : Nat} {arguments : List Arg} {ids : List ValueId} {retained : List (ValueId × RetainedAlias)}
    (rows : GeneratedCallArgumentRows access path index arguments ids retained)
    {argument : Arg} {id : ValueId} {aliases : List RetainedAlias}
    (query : access.aliasArg (path ++ [index + arguments.length]) argument = .ok aliases) :
    GeneratedCallArgumentRows access path index (arguments ++ [argument]) (ids ++ [id])
      (retained ++ aliases.map (fun alias => (id, alias))) := by
  induction rows with
  | nil index =>
    simpa using (GeneratedCallArgumentRows.cons query (GeneratedCallArgumentRows.nil (index + 1)))
  | @cons index head rest value ids priorAliases retained priorQuery tail ih =>
    have nextQuery : access.aliasArg (path ++ [(index + 1) + rest.length]) argument = .ok aliases := by
      have equal : index + (head :: rest).length = (index + 1) + rest.length := by simp; omega
      rw [← equal]
      exact query
    have next := ih nextQuery
    simpa only [List.cons_append, List.append_assoc] using (GeneratedCallArgumentRows.cons priorQuery next)

theorem ArgSource.byVal_callChild {cfg : Cfg} {env : Env} {initial state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initial)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv (callArgContext root.context index (.byVal expression) found)) :
    root.ChildAt child index (by simp [DemandNode.child?, DemandNode.children, found]) := by
  obtain ⟨plans, path, world, typing, roots, context⟩ := canonical
  have childContext : HEq child.context
      (root.context.child rfl index (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, found]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using context
  refine ⟨world, path, plans, childContext, typing, roots, ?_⟩
  intro alias member
  have retained := callArgContext_retained_subset root.context index (.byVal expression) found member
  have eq := demandContextRetainedEq plans path rfl childContext
  simpa only [callArgContext, ArgContext.retained, eq] using retained

theorem ExprSource.callArgumentAlias {cfg : Cfg} {env : Env} {state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) state)
    {index : Nat} {argument : Arg} (found : arguments[index]? = some argument)
    (shrink : cfg.mod.profile = .shrink) :
    ∃ aliases, source.rootsEnv.access.aliasArg (source.path ++ [index]) argument = .ok aliases := by
  have access := source.access
  cases contextEq : source.context with
  | pilot profile active => exact False.elim (by rw [shrink] at profile; cases profile)
  | @shrink planContext profile context =>
    rw [contextEq] at access
    have accessEq : planContext.approvals.access = source.rootsEnv.access := by
      have moduleEq := access.2.2.1
      have implementationEq := access.2.2.2.1
      have contextEq := access.2.2.2.2
      cases accessAt : planContext.approvals.access
      rw [accessAt] at moduleEq implementationEq contextEq
      unfold PEnv.access
      congr 1
    simpa only [accessEq] using context.call_argument_alias index argument found

theorem ArgSource.byVal_callRetainsPrior {cfg : Cfg} {env : Env} {initial state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initial)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byVal expression) found))
    {ids : List ValueId} {prior : List (ValueId × RetainedAlias)}
    (rows : GeneratedCallArgumentRows root.rootsEnv.access root.path 0 (arguments.take index) ids prior)
    (shrink : cfg.mod.profile = .shrink) : ∀ cell ∈ prior, cell.2 ∈ child.context.retained := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  have childContext : HEq child.context
      (root.context.child rfl index (.expression expression) .expression
        (by simp [DemandNode.child?, DemandNode.children, found]) (by trivial)) := by
    simpa only [ArgSource.MatchesContext, callArgContext] using childContext
  have retainedEq := demandContextRetainedEq plans path rfl childContext
  rw [retainedEq]
  have access := root.access
  cases contextEq : root.context with
  | pilot profile active => exact False.elim (by rw [shrink] at profile; cases profile)
  | @shrink planContext profile context =>
    rw [contextEq] at access
    have accessEq : planContext.approvals.access = root.rootsEnv.access := by
      have moduleEq := access.2.2.1
      have implementationEq := access.2.2.2.1
      have contextEq := access.2.2.2.2
      cases accessAt : planContext.approvals.access
      rw [accessAt] at moduleEq implementationEq contextEq
      unfold PEnv.access
      congr 1
    intro cell member
    obtain ⟨earlier, argument, aliases, argumentAt, idAt, query, aliasMember⟩ := rows.member_origin member
    have earlierBound : earlier < index := by
      have bound := (List.getElem?_eq_some_iff.mp argumentAt).1
      simp only [List.length_take] at bound
      omega
    have originalAt : arguments[earlier]? = some argument := by
      simpa [earlierBound] using argumentAt
    have included := callArgContext_prefix_alias context profile index (.byVal expression) found earlierBound originalAt
      (by simpa only [accessEq, Nat.zero_add] using query) aliasMember
    simpa only [callArgContext, ArgContext.retained, contextEq] using included

theorem ArgSource.byVal_callMetadata {cfg : Cfg} {env : Env} {initial state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initial)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byVal expression) found)) :
    child.typingEnv = root.typingEnv ∧ child.rootsEnv = root.rootsEnv := by
  exact ⟨canonical.2.2.2.1, canonical.2.2.2.2.1⟩

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
#print axioms GeneratedCallArgumentRows.snoc
#print axioms GeneratedCallArgumentRows.member_origin
#print axioms ArgSource.byVal_callRetainsPrior
#print axioms ExprSource.callArgumentAlias
#print axioms ExprSource.callArgsCanonical
#print axioms ArgSource.byVal_callChild
#print axioms ArgSource.byVal_callMetadata
#print axioms ArgsSource.atFuel_callChildren
#print axioms ArgsSource.afterHead_callChildren
end Goose.Lower
