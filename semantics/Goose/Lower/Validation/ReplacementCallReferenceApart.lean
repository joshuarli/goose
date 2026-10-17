import Goose.Lower.Validation.ReplacementDemandQueries
import Goose.Lower.Validation.AdmittedSourceCallArgumentTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation

theorem _root_.Goose.Core.DemandNodeAt.call_reference_argument {root : DemandNode} {path : List Nat}
    {function : ContextId} {arguments : List Arg} {origin : OriginId} {index : Nat}
    {mutability : Mutability} {place : Place}
    (source : DemandNodeAt root path (.expression (.call function arguments origin)))
    (argument : arguments[index]? = some (.byRef mutability place)) :
    DemandNodeAt root (path ++ [index]) (.place place) := by
  apply source.snoc index
  simp only [DemandNode.child?, DemandNode.children, List.getElem?_map, argument,
    Option.map_some, Option.join_some]

theorem ReplacementDemandContext.reference_argument_query_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {suffix : List Nat} {function : ContextId} {arguments : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call function arguments callOrigin)))
    {index : Nat} {mutability : Mutability} {argumentPlace : Place}
    (argument : arguments[index]? = some (.byRef mutability argumentPlace))
    {env : PEnv} {before after : RState} {argumentRoots : List (List RootRef)} {roots : List RootRef}
    (replayed : rpArgs env arguments before = .ok (argumentRoots, after))
    (rootAt : argumentRoots[index]? = some roots)
    (access : env.access = context.planContext.approvals.access)
    {target : DemandOwner}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner)
      (target.roots.flatMap func.expandParameterRoot))
    (sourceKnown : ReplacementRootsWithin query (roots.flatMap func.expandParameterRoot)) :
    ReplacementApart queries owner query := by
  have child := source.call_reference_argument argument
  obtain ⟨childBefore, childAfter, childReplay⟩ :=
    AdmittedSourceCalls.rpArgs_argument_replay argument replayed rootAt
  obtain ⟨_, actualRoots, _, rootsAt, _⟩ := context.descendant_place_disjoint child
  apply context.descendant_place_query_apart child targetAt rootsAt closed ownerKnown
  exact sourceKnown.access_place childReplay (access ▸ rootsAt)

#print axioms DemandNodeAt.call_reference_argument
#print axioms ReplacementDemandContext.reference_argument_query_apart

end Goose.Lower.Validation
