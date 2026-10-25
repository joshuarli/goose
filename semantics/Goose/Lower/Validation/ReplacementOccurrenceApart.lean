import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger
import Goose.Lower.Validation.ReplacementDemandQueries

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem ReplacementContentFlowSource.ReadOccurrence.apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (context : ReplacementDemandContext module planOwner path place rhs origin)
    {env : PEnv} {func : Func} {upper : Prov} {address value : ValueId}
    (occurrence : ReadOccurrence env (.expression rhs) func upper value address)
    (access : env.access = context.planContext.approvals.access)
    {target : DemandOwner}
    (targetAt : context.planContext.approvals.access.owner place = .ok target)
    {girModule : GIR.Module} {types : Array (Option VTy)} {queries : ReplacementQueries} {owner : ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (addressKnown : ReplacementRootsWithin (queries.ownerDependencies address)
      ((rootsAt upper.vals address).flatMap func.expandParameterRoot))
    (valueKnown : ReplacementRootsWithin (queries.ownerDependencies value)
      ((rootsAt upper.vals value).flatMap func.expandParameterRoot)) :
    ReplacementInstApart girModule types queries owner (.def value (.load address)) := by
  obtain ⟨localEnv, suffix, child, before, addressRoots, addressAfter, readRoots, readAfter,
    localAccess, source, addressReplay, readReplay, _, _, addressRefined, valueRefined, _⟩ := occurrence
  exact context.descendant_replay_read_load_apart source targetAt (localAccess.trans access)
    addressReplay readReplay closed ownerKnown
    (addressKnown.refined_expanded closed addressRefined)
    (valueKnown.refined_expanded closed valueRefined)

#print axioms ReplacementContentFlowSource.ReadOccurrence.apart

end Goose.Lower.Validation
