import Goose.Lower.DemandCallSliceMixedBody
import Goose.Lower.DemandCallSliceTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_slice_mixed_callee_terminal {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : SliceMixedStatements cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts)
    (noResults : impl.results.toList = []) (noValue : impl.body.value = none)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod env.vars impl.results.toList) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod (lowerContextAt cfg.mod ctx impl)
      (lowerEnv cfg.mod env.vars impl.results.toList) root source.path (.block none (callPre impl) false impl.body) (callEntry impl))
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (callEntry impl).vals.size) {initial : GIR.Frame}
    (cells : PreRel initial (callPre impl) pre)
    (realized : map.Realizes cfg.mod source.world env ⟨(0, 0), initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
      impl.results.toList none source.typingEnv source.rootsEnv (callEntry impl) initial (0, 0))
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ (lowerContextAt cfg.mod ctx impl) (0, 0) initial state)
    {taken : Nat} {terminal : DemandRuntimePoint}
    (steps : DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
      ⟨(0, 1 + (callPre impl).length), { initial with scopes := (impl.body.scope, state.nextScope) :: initial.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ terminal)
    {term : Term} (terminalAt : instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term))
    {targetFuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ targetFuel terminal next) :
    ∃ fuel, execBlock fuel cfg env pre impl.body state = .ok (.normal .unit) terminal.state ∧
      BlockResult source (.normal .unit) terminal.state ∧
      (∃ total, DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ total
        ⟨(0, 0), initial, state⟩ terminal) ∧
      Post cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
        (callEntry impl) initial
        (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)).2
        terminal.frame terminal.point [] ∧ map.Realizes cfg.mod source.world env terminal := by
  apply accepted_generated_parameterized_callee_terminal_of_family source envVars noResults noValue selected owned occurrence rows
    coverage admitted bounded cells realized input entry (@SliceMixedCursor cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList root owner selected)
    (accepted_generated_slice_mixed_statements fragment selected (callEntry impl) (callPre impl) false impl.body).1 (fun done => fragment.normal done) ?_ steps terminalAt maximal
  intro statement innerState child childBefore childBuilt childInitial childStart childMap childRequired runtime current term terminal fuel maximal
  exact current.excludes_maximal_terminal terminal maximal


#print axioms accepted_generated_parameterized_slice_mixed_callee_terminal
end Goose.Lower
