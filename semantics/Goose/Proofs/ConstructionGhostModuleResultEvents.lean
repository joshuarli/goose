import Goose.Proofs.ConstructionGhostActivationResultEvents
import Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents
import Goose.Proofs.ConstructionGhostInvocationVisitEvents

namespace Goose.Proofs.ConstructionGhostModuleResultEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostActivationResultEvents Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Proofs.ConstructionGhostActivationEvents Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationVisitEvents Goose.Proofs.ConstructionGhostSourceFuel

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem entryCallResult_resultPrefix (outcome : ExecutionStep (List Carrier)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (entryCallResult outcome)).construction.events := by
  apply (eventPrefix_iff_isPrefix _ _).mpr
  cases outcome with
  | ok carriers state =>
      have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events) (publishCarriers 0 carriers) :=
        preservesConstructionInvariant_publishCarriers 0 carriers
      exact kept state List.prefix_rfl
  | stop | escape | jump => exact List.prefix_rfl

theorem deliverCarriers_resultPrefix (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (origin : Goose.Core.OriginId) (outcome : ExecutionStep (List Carrier)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (((show EvalM (List Carrier) from fun _ => outcome) >>= fun carriers =>
        deliverCarriers fuel layout channels carriers origin) (Goose.Proofs.Exit.stepState outcome))).construction.events := by
  apply (eventPrefix_iff_isPrefix _ _).mpr
  cases outcome with
  | ok carriers state =>
      have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (deliverCarriers fuel layout channels carriers origin) :=
        preservesConstructionInvariant_deliverCarriers fuel layout channels carriers origin
      exact kept state List.prefix_rfl
  | stop | escape | jump => exact List.prefix_rfl

theorem call_resultPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (pre : List (Goose.Core.VarId × Value)) (scope : Nat)
    (statements : List Stmt) (tail : Option Expr) (activated : ExecutionState)
    (channels : List Channel) (origin : Goose.Core.OriginId) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (execution : execActivationBody (fuel + 1) config activation pre implementation.body activated =
      activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
        resultScopeContinuation activation.channels tail
          (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
            (fun channels => evalProduce fuel config
              { activation with scopes := (scope, activated.nextScope) :: activation.scopes } channels expression)) outcome)
        (resultScopeStart activation scope activated)))
    (call : callResult = ((enterActivation (fuel + 2) config activation pre implementation.body origin >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers origin) activated)) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events := by
  have bodyPrefix := activationBody_resultPrefix fuel config activation pre scope statements tail activated outcome (by simpa [body] using execution)
  have activationPrefix := finishActivation_resultPrefix config.layout activation (implementation.results.toList.map (·.ty)) origin
    (execActivationBody (fuel + 1) config activation pre (.mk scope statements tail)) activated
  have entered : enterActivation (fuel + 2) config activation pre implementation.body origin activated =
      finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
        (execActivationBody (fuel + 1) config activation pre (.mk scope statements tail)) activated := by
    simp [enterActivation, found, body]
  have delivered := deliverCarriers_resultPrefix (fuel + 2) config.layout channels origin
    (enterActivation (fuel + 2) config activation pre implementation.body origin activated)
  have deliveryEq : ((enterActivation (fuel + 2) config activation pre implementation.body origin >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers origin) activated) =
      (((show EvalM (List Carrier) from fun _ => enterActivation (fuel + 2) config activation pre implementation.body origin activated) >>= fun carriers =>
        deliverCarriers (fuel + 2) config.layout channels carriers origin)
        (Goose.Proofs.Exit.stepState (enterActivation (fuel + 2) config activation pre implementation.body origin activated))) := by
    cases result : enterActivation (fuel + 2) config activation pre implementation.body origin activated <;> simp [bind, result, Goose.Proofs.Exit.stepState]
  rw [← deliveryEq, ← call] at delivered
  exact eventPrefix_trans _ _ _ bodyPrefix
    (eventPrefix_trans _ _ _ (by simpa [entered] using activationPrefix) delivered)

theorem moduleEntry_tail_resultPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (activated before : ExecutionState)
    (channels : List Channel) (callResult : ExecutionStep (List Carrier)) (outcome : ExecutionStep Flow)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (execution : execActivationBody (fuel + 1) config activation [] (.mk scope statements tail) activated =
      activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
        resultScopeContinuation activation.channels tail
          (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
            (fun channels => evalProduce fuel config
              { activation with scopes := (scope, activated.nextScope) :: activation.scopes } channels expression)) outcome)
        (resultScopeStart activation scope activated)))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config before = entryCallResult callResult) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events := by
  have kept := call_resultPrefix fuel config activation implementation [] scope statements tail activated channels 0
    callResult outcome found body (by simpa [body] using execution) call
  rw [moduleResult]
  exact eventPrefix_trans _ _ _ kept (entryCallResult_resultPrefix callResult)

theorem moduleEntry_tail_visitPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (activated before : ExecutionState)
    (channels : List Channel) (callResult : ExecutionStep (List Carrier)) (outcome : ExecutionStep Flow)
    (visits : List StatementInvocation) (visit : StatementInvocation)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config before = entryCallResult callResult) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events := by
  have bound : bindAll activation.act activated.nextScope [] (resultScopeStart activation scope activated) =
      .ok () (resultScopeStart activation scope activated) := by simp [bindAll, bind, pure]
  obtain ⟨other, otherVisits, chunks, otherReplay, ordered, once, aligned, finalEq, execution, sources⟩ :=
    activationBody_fixedSourceEvents fuel config activation [] scope statements tail activated
      (resultScopeStart activation scope activated) bound supported
  have same : other = outcome := otherReplay.sound.symm.trans replay.sound
  subst other
  have kept := moduleEntry_tail_resultPrefix fuel config activation implementation scope statements tail activated before channels
    callResult outcome found body execution call moduleResult
  have visitsKept := invocationEvents_visitPrefix (statementReplay_invocationEvents replay) (statementInvocation visit)
    (List.mem_map.mpr ⟨visit, member, rfl⟩)
  exact eventPrefix_trans _ _ _ visitsKept kept

theorem moduleEntry_resultPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (activated before : ExecutionState)
    (channels : List Channel) (callResult : ExecutionStep (List Carrier)) (outcome : ExecutionStep Flow)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements none)
    (execution : execActivationBody (fuel + 1) config activation [] (.mk scope statements none) activated =
      activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
        resultScopeContinuation activation.channels none
          (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
            (fun channels => evalProduce fuel config
              { activation with scopes := (scope, activated.nextScope) :: activation.scopes } channels expression)) outcome)
        (resultScopeStart activation scope activated)))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config before = entryCallResult callResult) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events := by
  exact moduleEntry_tail_resultPrefix fuel config activation implementation scope statements none activated before channels
    callResult outcome found body execution call moduleResult

theorem moduleEntry_visitPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (activated before : ExecutionState)
    (channels : List Channel) (callResult : ExecutionStep (List Carrier)) (outcome : ExecutionStep Flow)
    (visits : List StatementInvocation) (visit : StatementInvocation)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements none)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config before = entryCallResult callResult) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config before)).construction.events := by
  exact moduleEntry_tail_visitPrefix fuel config activation implementation scope statements none activated before channels
    callResult outcome visits visit found body replay member supported call moduleResult

#print axioms call_resultPrefix
#print axioms moduleEntry_tail_visitPrefix
#print axioms moduleEntry_tail_resultPrefix
#print axioms moduleEntry_visitPrefix
#print axioms moduleEntry_resultPrefix
#print axioms entryCallResult_resultPrefix
#print axioms deliverCarriers_resultPrefix
end Goose.Proofs.ConstructionGhostModuleResultEvents
