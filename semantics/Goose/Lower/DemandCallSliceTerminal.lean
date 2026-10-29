import Goose.Lower.DemandCallSliceBody
import Goose.Lower.DemandCallBodyReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem SliceAssignmentCursor.excludes_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceAssignmentCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) : False := by
  rcases cursor.nonterminal with ⟨id, op, found⟩ | ⟨effect, found⟩ <;> cases found.symm.trans terminal

theorem GeneratedSequencePrefixCursor.slice_excludes_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@SliceAssignmentCursor cfg env cx results)
      map required cx results before none bindings block selected source initial runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  apply cursor.excludes_maximal_terminal ?_ terminal maximal
  intro statement state source before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_terminal terminal

#print axioms SliceAssignmentCursor.excludes_terminal
#print axioms GeneratedSequencePrefixCursor.slice_excludes_terminal

theorem accepted_generated_parameterized_slice_callee_terminal {cfg : Cfg} {ctx : Context} {impl : Impl} {env : Env}
    {pre : List (VarId × Val)} {state : St} (source : BlockSource cfg env pre impl.body state)
    (envVars : env.vars = impl.vars)
    (fragment : SliceAssignmentStatements impl.body.stmts)
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
    accepted_generated_parameterized_slice_body_canonical source fragment selected owned occurrence rows coverage admitted bounded cells realized input extended entry
      (by simpa using steps)
  cases decomposition.progress with
  | interior cursor => exact (cursor.slice_excludes_terminal terminalAt maximal).elim
  | @complete sourceFuel consumed remaining boundary flow count executed residual evaluated ending =>
    have statements : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
        impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) boundary.state := by
      simp only [prepareLoopFlow_none, bind_apply] at evaluated
      cases raw : execStmts sourceFuel cfg { env with scopes := (impl.body.scope, state.nextScope) :: env.scopes }
          impl.body.stmts { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } with
      | stop stop after => simp [raw] at evaluated
      | ok rawFlow after =>
        have normal := fragment.normal raw
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


#print axioms accepted_generated_parameterized_slice_callee_terminal
end Goose.Lower
