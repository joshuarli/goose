import Goose.Lower.DemandCallParameterizedSequence
import Goose.Lower.DemandCallFallthrough
import Goose.Lower.DemandBranchTerminal
import Goose.Lower.DemandWhileEntryReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_callee_terminal_of_family {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
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
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } statement innerState →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (family : GeneratedSequencePrefixFamily (env := { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes })
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList selected (callEntry impl)
      none (callPre impl) false impl.body impl.body.stmts cursor)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } impl.body.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (excludes : ∀ {statement : Stmt} {innerState : St} (child : StmtSource cfg
      { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } statement innerState)
      {childBefore childBuilt : LS} {childInitial : GIR.Frame} {childStart : Pt} {childMap childRequired : RetainedSsaMap}
      {runtime : DemandRuntimePoint}, cursor child childBefore childBuilt childInitial childStart childMap childRequired runtime →
      ∀ {term : Term}, instAt (lowerContextAt cfg.mod ctx impl) runtime.point = some (.term term) →
      ∀ {fuel : Nat}, (∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ fuel runtime next) → False)
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
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩
  have extended : ExtT (lowerBlock none (callPre impl) false impl.body
      (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).2 cx.fn.blocks := by
    let le := lowerEnv cfg.mod impl.vars impl.results.toList
    let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
    have tailExtension : ExtT (Goose.Proofs.Lower.bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
      rw [lowerContextAt_blocks, lowerImpl_call_blocks]
      exact Goose.Proofs.Lower.extT_finish _
    have bodyExtension := tailExtension.of_adv
      (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
        (Goose.Proofs.Lower.bodyTail impl le body.1 body.2) rfl)
    simpa only [envVars] using bodyExtension
  have prologue := accepted_block_parameter_prologue_trace source
    (show lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) =
      ((lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).1,
        (lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl)).2) from rfl)
    input.atPoint extended input.related cells pre.length (by omega)
  have wholeTrace : DemandRuntimePrefix cx (pre.length + 1 + taken) ⟨(0, 0), initial, state⟩ terminal := by
    apply prologue.append
    simpa [cells.length] using steps
  obtain ⟨body, bodyOffset, bodyCanonical, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted, bodyEntryBounded, bodyEntryRealized, bodyInput, bodyProloguePost, decomposition, bodyReached⟩ :=
    accepted_generated_parameterized_body_family_canonical source selected owned occurrence rows coverage admitted bounded cells realized input extended entry cursor family
      (by simpa using steps)
  cases decomposition.progress with
  | interior current =>
    apply (current.excludes_maximal_terminal ?_ terminalAt maximal).elim
    intro statement innerState child childBefore childBuilt childInitial childStart childMap childRequired runtime current term terminal fuel maximal
    exact excludes child current terminal maximal
  | @complete sourceFuel consumed remaining boundary flow count executed residual evaluated ending =>
    have statements : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
        impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) boundary.state := by
      simp only [prepareLoopFlow_none, bind_apply] at evaluated
      cases raw : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
          impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } with
      | stop stop after => simp [raw] at evaluated
      | ok rawFlow after =>
        have normal := normal raw
        subst rawFlow
        simp only [raw, prepareReturn, pure_apply, Res.ok.injEq] at evaluated
        obtain ⟨_, rfl⟩ := evaluated
        rfl
    have normal : flow = .normal .unit := by
      simp only [prepareLoopFlow_none, bind_apply, statements, prepareReturn, pure_apply, Res.ok.injEq] at evaluated
      exact evaluated.1.symm
    subst flow
    cases ending with
    | transfer abnormal _ => exact (abnormal .unit rfl).elim
    | normal sequencePost result bodyBounded bodyRealized =>
      have nextPost : Post cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes } cx
          (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) (callPre impl) impl.body)
          { initial with scopes := (impl.body.scope, state.nextScope) :: initial.scopes }
          (lowerStmts none impl.body.stmts (lowerEnv cfg.mod env.vars impl.results.toList)
            (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars impl.results.toList) (callEntry impl) (callPre impl) impl.body)).2
          boundary.frame boundary.point [] := by
        simpa [bodyOffset, lowerStmts, pure_run] using sequencePost
      rcases residual.uncons with ⟨_, same⟩ | ⟨rest, afterLeave, length, leaveStep, tail⟩
      · subst terminal
        have site := GeneratedDemandInstruction.blockLeave_auto occurrence rows (by simpa [noValue, lowerBlockValue, demandBlockValueBefore, pure_run] using nextPost.pp) extended
        cases site.instruction.symm.trans terminalAt
      · obtain ⟨bodyDone, finalPost, bodyResult, finalBounded, finalRealized⟩ :=
          accepted_generated_parameterized_body_leave source selected owned occurrence rows coverage admitted bounded cells realized input extended entry noValue statements nextPost leaveStep
        have fallthrough := generated_callee_unit_fallthrough noResults noValue (by simpa [envVars] using finalPost)
        rcases tail.uncons with ⟨_, rfl⟩ | ⟨_, _, _, nextStep, _⟩
        · exact ⟨sourceFuel + 1, bodyDone, bodyResult, ⟨_, wholeTrace⟩, by simpa [envVars] using finalPost, finalRealized⟩
        · exact (runtimeStep_excludes_return fallthrough nextStep).elim



#print axioms accepted_generated_parameterized_callee_terminal_of_family
end Goose.Lower
