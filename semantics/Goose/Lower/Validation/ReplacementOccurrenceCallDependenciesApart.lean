import Goose.Lower.Validation.ReplacementDemandCallSummary
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlow.Model

theorem CallOccurrence.dependencies_apart_of_callRoots {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {env : PEnv} (environment : env.mod = module)
    (access : env.access = demand.planContext.approvals.access)
    {func : Func} {types : Array (Option VTy)} {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    {queries : ReplacementQueries} {owner value function : ValueId} {arguments : List ValueId}
    {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (occurrence : CallOccurrence env (.expression rhs) func upper value function arguments callOrigin)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (argumentApart : ∀ argument ∈ arguments, ReplacementApart queries owner (queries.ownerDependencies argument))
    (calledApart : ReplacementApart queries owner (queries.callRoots function arguments)) :
    ReplacementApart queries owner (callDependencies (lower module) types queries function arguments) := by
  apply callDependencies_apart (fun argument member _ => argumentApart argument member) calledApart
  obtain ⟨localEnv, sourcePath, syntaxArgs, sourceOrigin, before, sourceRoots, argumentsAfter,
    returned, after, localAccess, _, source, replayed, contentsChecked, callReplayed, _, _, argumentOrigins, _, trace⟩ := occurrence
  have moduleEq : localEnv.mod = module := (congrArg AccessEnv.mod localAccess).trans environment
  obtain ⟨context, impl, contextAt, implAt, _, _, _⟩ :=
    rpCall_ok localEnv function sourceRoots argumentsAfter returned after callReplayed
  have contextRow : module.contexts[function]? = some context := by simpa only [moduleEq] using contextAt
  have implRow : module.impls[context.impl]? = some impl := by simpa only [moduleEq] using implAt
  have loweredAt := lower_func_at contextRow implRow
  cases summaryAt : impl.summary with
  | unknown =>
    have loweredSummary : (lowerContextAt module context impl).summary = .unknown := summaryAt
    simpa only [callSummaryRoots, loweredAt, loweredSummary] using calledApart
  | known summary =>
    have accessModule : demand.planContext.approvals.access.mod = module :=
      (congrArg AccessEnv.mod access).symm.trans environment
    obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
    have same : callSite.callee = lowerContextAt module context impl :=
      Option.some.inj (callSite.calleeAt.symm.trans loweredAt)
    have parameterCount : (lowerContextAt module context impl).params.length = impl.params.size := by
      simp only [lowerContextAt, lowerImpl, lowerImplFromState, List.length_map, Array.length_toList]
    apply demand.known_call_summary_apart_of_accepted accepted accessModule source contextRow implRow summaryAt
      targetAt closed ownerKnown ?_ argumentApart
    intro index bound
    obtain ⟨argument, argumentAt, _⟩ := callSite.arguments index (by simpa only [same, parameterCount] using bound)
    exact ⟨argument, argumentAt⟩

#print axioms CallOccurrence.dependencies_apart_of_callRoots

end Goose.Lower.Validation.ReplacementContentFlowSource
