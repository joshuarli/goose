import Goose.Proofs.ConstructionGhostArrayCallEvents
import Goose.Proofs.ConstructionGhostModuleResultEvents
import Goose.Proofs.ConstructionGhostDeclaration
import Goose.Proofs.ConstructionGhostCallSetupHistory
import Goose.Proofs.ConstructionGhostCallPathEvents

namespace Goose.Proofs.ConstructionGhostModuleArrayCallEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostArrayCallEvents
open Goose.Proofs.ConstructionGhostModuleResultEvents Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostDeclaration Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostCallSetupHistory
open Goose.Proofs.ConstructionGhostCallPathEvents Goose.Proofs.ConstructionGhostCallArguments
open Goose.Proofs.ConstructionGhostCallActivation Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostStatementPaths

theorem moduleEntry_arrayCallEvents (fuel sourceFuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (activated moduleBefore : ExecutionState) (channels : List Channel) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (arrayOrigin origin : Goose.Core.OriginId)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (visitFuel : visit.fuel = sourceFuel + 4)
    (visitStatement : visit.statement = .letS localVar (.arrLit ty operands arrayOrigin) origin)
    (supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config moduleBefore = entryCallResult callResult)
    (occurrence : DeclarationOccurrence (sourceFuel + 3) config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } localVar (.arrLit ty operands arrayOrigin)
      origin visit.before (some incoming) initial)
    (renewed : liftConstruction arrayOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (destinationFound : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (nonfixed : element.nonfixed = true)
    (elementsSupported : ∀ operand ∈ operands, FuelSupport config (sourceFuel + 2)
      (.element { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)) :
    ∃ elementOutcome elementVisits,
      OperandReplay (fun operand => buildElement (sourceFuel + 2) config
        { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)
        0 operands [] ready elementOutcome elementVisits ∧
      elementVisits.map Invocation.operand = operands.take elementVisits.length ∧
      (elementVisits.map Invocation.ordinal).Nodup ∧
      ∀ elementVisit ∈ elementVisits, ∀ context arguments callOrigin layout layoutReady childReady child destination callReady,
        elementVisit.operand = .call context arguments callOrigin →
        receivingLayout config.layout element elementVisit.before = .ok layout layoutReady →
        receivingAction (expressionOrigin elementVisit.operand) current (fun parent => openChild parent element layout) layoutReady = .ok child childReady →
        liftConstruction callOrigin (renewReceivingDestination child) childReady = .ok destination callReady →
        SourceHistory config sourceFuel ((((path ++ [0]) ++ [elementVisit.ordinal]) ++ [0]) ++ [0])
          (.channelCall { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
            context arguments [.construct destination] callOrigin) callReady
          (invokeCall sourceFuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
            context arguments [.construct destination] callOrigin callReady) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (invokeCall sourceFuel config
          { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          context arguments [.construct destination] callOrigin callReady)).construction.events
          (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config moduleBefore)).construction.events := by
  obtain ⟨elementOutcome, elementVisits, elementReplay, ordered, once, children⟩ :=
    array_constructedCallEvents sourceFuel config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } path localVar incoming current ty operands arrayOrigin origin
      visit.before initial prepared ready pending element occurrence renewed destinationFound elementFound nonfixed elementsSupported
  refine ⟨elementOutcome, elementVisits, elementReplay, ordered, once, ?_⟩
  intro elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady operandEq layoutResult opened callRenewed
  obtain ⟨childHistory, childPrefix⟩ := children elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady
    operandEq layoutResult opened callRenewed
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement] at actual
  rw [actual] at childPrefix
  have modulePrefix := moduleEntry_tail_visitPrefix fuel config activation implementation scope statements tail activated moduleBefore
    channels callResult outcome visits visit found body replay member supported call moduleResult
  exact ⟨childHistory, eventPrefix_trans _ _ _ childPrefix modulePrefix⟩

theorem moduleEntry_arrayCallSetup (fuel callFuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (activated moduleBefore : ExecutionState) (channels : List Channel) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (arrayOrigin origin : Goose.Core.OriginId)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (visitFuel : visit.fuel = callFuel + 5)
    (visitStatement : visit.statement = .letS localVar (.arrLit ty operands arrayOrigin) origin)
    (supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config moduleBefore = entryCallResult callResult)
    (occurrence : DeclarationOccurrence (callFuel + 4) config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } localVar (.arrLit ty operands arrayOrigin)
      origin visit.before (some incoming) initial)
    (renewed : liftConstruction arrayOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (destinationFound : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (nonfixed : element.nonfixed = true)
    (elementsSupported : ∀ operand ∈ operands, FuelSupport config (callFuel + 3)
      (.element { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)) :
    ∃ elementOutcome elementVisits,
      OperandReplay (fun operand => buildElement (callFuel + 3) config
        { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)
        0 operands [] ready elementOutcome elementVisits ∧
      elementVisits.map Invocation.operand = operands.take elementVisits.length ∧
      (elementVisits.map Invocation.ordinal).Nodup ∧
      ∀ elementVisit ∈ elementVisits, ∀ context arguments callOrigin layout layoutReady childReady child destination callReady,
        elementVisit.operand = .call context arguments callOrigin →
        receivingLayout config.layout element elementVisit.before = .ok layout layoutReady →
        receivingAction (expressionOrigin elementVisit.operand) current (fun parent => openChild parent element layout) layoutReady = .ok child childReady →
        liftConstruction callOrigin (renewReceivingDestination child) childReady = .ok destination callReady →
        CallSetupHistory callFuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          ((((path ++ [0]) ++ [elementVisit.ordinal]) ++ [0]) ++ [0]) context arguments [.construct destination] callOrigin callReady ∧
        EventPrefix (Goose.Proofs.Exit.stepState (invokeCall (callFuel + 1) config
          { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          context arguments [.construct destination] callOrigin callReady)).construction.events
          (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config moduleBefore)).construction.events := by
  obtain ⟨elementOutcome, elementVisits, elementReplay, ordered, once, children⟩ :=
    moduleEntry_arrayCallEvents fuel (callFuel + 1) config activation implementation scope statements tail activated moduleBefore
      channels callResult outcome visits visit path localVar incoming current ty operands arrayOrigin origin initial prepared ready pending element
      found body replay member (by simpa [Nat.add_assoc] using visitFuel) visitStatement supported call moduleResult
      (by simpa [Nat.add_assoc] using occurrence) renewed destinationFound elementFound nonfixed
      (by simpa [Nat.add_assoc] using elementsSupported)
  refine ⟨elementOutcome, elementVisits, elementReplay, ordered, once, ?_⟩
  intro elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady operandEq layoutResult opened callRenewed
  obtain ⟨history, kept⟩ := children elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady
    operandEq layoutResult opened callRenewed
  exact ⟨invokeCall_setupHistory callFuel config _ _ context arguments [.construct destination] callOrigin callReady history, kept⟩

theorem moduleEntry_arrayCalleeEvents (fuel calleeFuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (activated moduleBefore : ExecutionState) (channels : List Channel) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (arrayOrigin origin : Goose.Core.OriginId)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (visitFuel : visit.fuel = calleeFuel + 7)
    (visitStatement : visit.statement = .letS localVar (.arrLit ty operands arrayOrigin) origin)
    (supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel
        (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config moduleBefore = entryCallResult callResult)
    (occurrence : DeclarationOccurrence (calleeFuel + 6) config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } localVar (.arrLit ty operands arrayOrigin)
      origin visit.before (some incoming) initial)
    (renewed : liftConstruction arrayOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (destinationFound : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (nonfixed : element.nonfixed = true)
    (elementsSupported : ∀ operand ∈ operands, FuelSupport config (calleeFuel + 5)
      (.element { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)) :
    ∃ elementOutcome elementVisits,
      OperandReplay (fun operand => buildElement (calleeFuel + 5) config
        { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)
        0 operands [] ready elementOutcome elementVisits ∧
      elementVisits.map Invocation.operand = operands.take elementVisits.length ∧
      (elementVisits.map Invocation.ordinal).Nodup ∧
      ∀ elementVisit ∈ elementVisits, ∀ context arguments callOrigin layout layoutReady childReady child destination callReady,
        elementVisit.operand = .call context arguments callOrigin →
        receivingLayout config.layout element elementVisit.before = .ok layout layoutReady →
        receivingAction (expressionOrigin elementVisit.operand) current (fun parent => openChild parent element layout) layoutReady = .ok child childReady →
        liftConstruction callOrigin (renewReceivingDestination child) childReady = .ok destination callReady →
        ∀ lookupReady argumentsReady valuesReady activationReady boundReady id callee callableChannels refreshed values,
          getImplementation config context callReady = .ok (id, callee) lookupReady →
          config.module.impls[id]? = some callee →
          [Channel.construct destination].length = callee.results.size →
          prepareCallableChannels { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
            [.construct destination] callee callOrigin lookupReady = .ok callableChannels argumentsReady →
          evalArguments (calleeFuel + 2) config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
            callee.vars callee.params.toList arguments argumentsReady = .ok values valuesReady →
          refreshCallableChannels callableChannels callOrigin valuesReady = .ok refreshed activationReady →
          activationReady.activations.length < Goose.Core.maxCallDepth →
          ∀ calleeScope calleeStatements calleeTail, callee.body = .mk calleeScope calleeStatements calleeTail →
          ClosedModuleWithTails config → (∀ statement ∈ calleeStatements, StatementSyntax config statement) →
          (let calleeActivation : RuntimeActivation := ⟨id, activationReady.nextAct, callee.vars, [], refreshed⟩
           let calleeActivated := { activationReady with nextAct := activationReady.nextAct + 1, activations := calleeActivation :: activationReady.activations }
           bindAll calleeActivation.act calleeActivated.nextScope
             ((callee.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
             (resultScopeStart calleeActivation calleeScope calleeActivated) = .ok () boundReady) →
          let calleeActivation : RuntimeActivation := ⟨id, activationReady.nextAct, callee.vars, [], refreshed⟩
          let calleeActivated := { activationReady with nextAct := activationReady.nextAct + 1, activations := calleeActivation :: activationReady.activations }
          let calleeEnvironment := { calleeActivation with scopes := (calleeScope, calleeActivated.nextScope) :: calleeActivation.scopes }
          ∃ calleeOutcome calleeVisits,
            StatementReplay config calleeEnvironment calleeFuel 0 calleeStatements boundReady calleeOutcome calleeVisits ∧
            (calleeVisits.map StatementInvocation.ordinal).Nodup ∧
            ∀ calleeVisit ∈ calleeVisits, ∃ suffix, StatementPath 0 suffix calleeVisit.ordinal ∧
              SourceHistory config calleeVisit.fuel
                ((((((((path ++ [0]) ++ [elementVisit.ordinal]) ++ [0]) ++ [0]) ++ [1]) ++ [0]) ++ [0]) ++ suffix)
                (.statement calleeEnvironment calleeVisit.statement) calleeVisit.before calleeVisit.outcome ∧
              EventPrefix (Goose.Proofs.Exit.stepState calleeVisit.outcome).construction.events
                (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config moduleBefore)).construction.events := by
  obtain ⟨elementOutcome, elementVisits, elementReplay, ordered, once, children⟩ :=
    moduleEntry_arrayCallEvents fuel (calleeFuel + 3) config activation implementation scope statements tail activated moduleBefore
      channels callResult outcome visits visit path localVar incoming current ty operands arrayOrigin origin initial prepared ready pending element
      found body replay member (by simpa [Nat.add_assoc] using visitFuel) visitStatement supported call moduleResult
      (by simpa [Nat.add_assoc] using occurrence) renewed destinationFound elementFound nonfixed
      (by simpa [Nat.add_assoc] using elementsSupported)
  refine ⟨elementOutcome, elementVisits, elementReplay, ordered, once, ?_⟩
  intro elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady operandEq layoutResult opened callRenewed
  obtain ⟨history, callPrefix⟩ := children elementVisit elementMember context arguments callOrigin layout layoutReady childReady child destination callReady
    operandEq layoutResult opened callRenewed
  intro lookupReady argumentsReady valuesReady activationReady boundReady id callee callableChannels refreshed values lookup implemented arity calleePrepared
    argumentsResult refresh depth calleeScope calleeStatements calleeTail calleeBody closed calleeSyntax bound
  obtain ⟨calleeOutcome, calleeVisits, calleeReplay, calleeOnce, calleeChildren⟩ :=
    call_statementPathEvents calleeFuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      ((((path ++ [0]) ++ [elementVisit.ordinal]) ++ [0]) ++ [0]) context arguments [.construct destination] callOrigin
      callReady lookupReady argumentsReady valuesReady activationReady boundReady id callee callableChannels refreshed values history
      lookup implemented arity calleePrepared argumentsResult refresh depth calleeScope calleeStatements calleeTail calleeBody closed calleeSyntax bound
  refine ⟨calleeOutcome, calleeVisits, calleeReplay, calleeOnce, ?_⟩
  intro calleeVisit member
  obtain ⟨suffix, suffixPath, childHistory, childPrefix⟩ := calleeChildren calleeVisit member
  exact ⟨suffix, suffixPath, childHistory, eventPrefix_trans _ _ _ childPrefix callPrefix⟩

#print axioms moduleEntry_arrayCalleeEvents
#print axioms moduleEntry_arrayCallSetup
#print axioms moduleEntry_arrayCallEvents
end Goose.Proofs.ConstructionGhostModuleArrayCallEvents
