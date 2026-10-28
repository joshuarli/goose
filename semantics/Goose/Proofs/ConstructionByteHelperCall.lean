import Goose.Proofs.ConstructionCallByteStatements
import Goose.Proofs.ConstructionAcceptedNestedActivation
import Goose.Proofs.ConstructionByteEntryStopped
import Goose.Proofs.ConstructionByteEntryScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem byteHelper_call_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (environment : RuntimeActivation) (contextId origin : Nat) (context : Context) (helper : Impl)
    (declarations : List ByteOwnerDeclaration)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[]) (results : helper.results = #[])
    (body : helper.body.stmts = declarations.map ByteOwnerDeclaration.statement) (tail : helper.body.value = none)
    (owners : ∀ declaration ∈ declarations, (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config environment contextId [] [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], []⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  have pushedWorld : AcceptedWorld config config.module.globals.size pushed (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_pushEmptyActivation config config.module.globals.size state ambient types live regions pending activation world rfl rfl
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments,
        timeout, EvalM.stop, bind, pure]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, enterActivation,
          execActivationBody, finishActivation, freshAct, EvalM.get, EvalM.set, timeout, EvalM.stop, bind, pure,
          Nat.not_le.mpr depth, activation, pushed]
        exact ⟨.callChannels activation [] :: ambient, types, live, regions, pushedWorld⟩
      | succ fuel =>
        obtain ⟨frame, actualActivation, initializedEq, environmentEq, actEq, scopes, channels, freshActed, freshScope,
          frameWorld, frameSource, position, phase, frameParameters, frameResults, original, originalAt, implAt, implId, vars⟩ :=
          acceptedEmptyCallPushedStatements config accepted state ambient types live regions pending contextId context helper
            contextAt helperAt parameters results world
        have originalEq : original = context := Option.some.inj (originalAt.symm.trans contextAt)
        subst original
        have helperEq : frame.source.impl = helper := Option.some.inj (implAt.symm.trans helperAt)
        have sameActivation : actualActivation = activation := by
          cases actualActivation with
          | mk impl act vars' scopes' channels' =>
            simp only at implId actEq vars scopes channels
            cases implId
            cases actEq
            rw [helperEq] at vars
            cases vars
            cases scopes
            cases channels
            rfl
        rw [sameActivation] at environmentEq frameWorld frameSource position channels
        let before := ownershipResultScopeState activation frame.source.impl.body.scope pushed
        let entryFrame := entryStatementsFrame config frame pushed.nextScope
        obtain ⟨next, nextTypes, nextLive, nextRegions, nextInitialized, extended, finalWorld, finalSource, finalFlow⟩ :=
          callByteStatements_accepted_world fuel config accepted frame contextId activation pushed before declarations ambient types live regions pending
            frameWorld frameSource position phase frameResults (by simpa only [helperEq] using body)
            (by simpa only [helperEq] using owners) checkFuel
        change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
          | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
        change AcceptedWorld config next.initialized
          (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
          (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending at finalWorld
        have initialized : next.initialized = config.module.globals.size := by
          simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initializedEq] using nextInitialized
        have invokeStep : invokeCall (fuel + 3) config environment contextId [] [] origin state =
            (finishActivation config.layout activation [] origin (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
              deliverCarriers (fuel + 2) config.layout [] carriers origin) pushed := by
          have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
            simp only [activation, helperEq]; exact helperAt
          simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments,
            enterActivation, lookup, frameResults, freshAct, EvalM.get, EvalM.set, bind, pure,
            Nat.not_le.mpr depth, activation, pushed]
          simp only [helperEq]
        rw [invokeStep]
        cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
        | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
        | stop reason after =>
          simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld
          have stopped' : execStmts fuel config
              { activation with scopes := (frame.source.impl.body.scope, pushed.nextScope) :: activation.scopes }
              frame.source.impl.body.stmts before = .stop reason after := by
            simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
          have stopped := execActivationBody_statements_stopped fuel config activation frame.source.impl.body pushed after reason stopped'
          simp only [bind, finishActivation, stopped]
          exact ⟨.callChannels activation [] :: ambient, nextTypes, nextLive, nextRegions, initialized ▸ finalWorld⟩
        | ok flow after =>
          simp only [outcome] at finalFlow
          subst flow
          simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld
          have normal : execStmts fuel config
              { activation with scopes := (frame.source.impl.body.scope, pushed.nextScope) :: activation.scopes }
              frame.source.impl.body.stmts before = .ok (.normal .unit) after := by
            simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
          let released := releaseScopeState activation frame.source.impl.body.scope pushed.nextScope after
          let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
          have done := execActivationBody_empty_normal fuel config activation frame.source.impl.body pushed after rfl
            (by simpa only [helperEq] using tail) normal
          have releaseWorld := finalWorld.releaseScope config next.initialized after (.callChannels activation [] :: ambient)
            nextTypes nextLive nextRegions pending activation frame.source.impl.body.scope pushed.nextScope
          have finishWorld := releaseWorld.finishEmptyCall config next.initialized released activation ambient nextTypes _ nextRegions pending outer
          simp [bind, finishActivation, done, finishChannels, landCarriersInto, deliverCarriers, pure, activation]
          exact ⟨nextTypes, _, nextRegions, initialized ▸ finishWorld⟩

#print axioms byteHelper_call_world
end Goose.Proofs.ConstructionAcceptedExecution
