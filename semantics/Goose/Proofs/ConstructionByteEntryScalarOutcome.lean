import Goose.Proofs.ConstructionByteEntryScalarTail
import Goose.Proofs.ConstructionByteEntryScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteEntry_scalarTail_outcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop) (declarations : List ByteOwnerDeclaration)
    (original : Context) (implementation : Impl) (expression : Expr)
    (world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = some expression)
    (form : AcceptedBinaryExpression expression)
    (enoughFuel : declarations.length + 2 ≤ fuel + 1)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
        let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      activation.channels = [] ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      invokeCall (fuel + 4) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 2) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 3) config.layout [] carriers 0) activated ∧
      (match outcome with
      | .stop reason after =>
        execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated = .stop reason after ∧
        AcceptedWorld config next.initialized after [.callChannels activation []] types nextLive regions []
      | .ok (.normal .unit) _ =>
        ∃ (tailFrame : ConstructionSourceFrame) (tailTypes : RootTypes) (tailLive : Goose.Core.RootInst → Prop)
          (tailRegions : List ReceivingRegion),
          let result := execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated
          match result with
          | .stop _ final => AcceptedWorld config tailFrame.initialized final [.callChannels activation []] tailTypes tailLive tailRegions []
          | .ok _ final | .escape _ _ final | .jump _ _ final =>
            AcceptedWorld config tailFrame.initialized final [.callChannels activation []] tailTypes
              (fun root => tailLive root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation frame.source.impl.body.scope activated.nextScope).contains root = false)
              tailRegions []
      | _ => False) := by
  obtain ⟨frame, activation, initializedEntry, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements_withInitialized config accepted state [] (declaredRootTypes config.module) live [] [] world
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have depth : state.activations.length < Goose.Core.maxCallDepth := by
    have runtime := world.ownership.runtime.activations
    cases active : state.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  have canonical : activation = ⟨original.impl, state.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars' scopes' channels' =>
      simp only at implId act vars scopes channels
      cases implId
      cases act
      cases vars
      cases scopes
      cases channels
      rfl
  have step := entryCallStep (fuel + 2) config ⟨0, 0, #[], [], []⟩ state original frame.source.impl originalAt implAt
    parameters results depth
  simp only [Nat.add_assoc] at step
  rw [← canonical] at step
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implId]
    exact implAt
  have entryAction : enterActivation (fuel + 3) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 2) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [entryAction] at step
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  obtain ⟨next, types, nextLive, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    entryByteStatements_accepted_world (fuel + 1) config accepted frame activation activated before declarations live
      frameWorld source position phase results (by simpa only [implementationEq] using body)
      (by simpa only [implementationEq] using owners) checkFuel
  change (match execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config next.initialized
    (Goose.Proofs.Exit.stepState (execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
    [.callChannels activation []] types nextLive regions [] at finalWorld
  refine ⟨frame, next, activation, types, nextLive, regions, channels, implementationEq, environmentEq, step, ?_⟩
  change (match execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .stop reason after => _ | .ok (.normal .unit) _ => _ | _ => False)
  cases outcome : execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
  | stop reason after =>
    have stopped : execStmts (fuel + 1) config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts before = .stop reason after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
    exact ⟨execActivationBody_statements_stopped (fuel + 1) config activation frame.source.impl.body activated after reason stopped,
      by simpa only [outcome, Goose.Proofs.Exit.stepState] using finalWorld⟩
  | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
  | ok flow after =>
    simp only [outcome] at finalFlow
    subst flow
    have statementsEq : frame.source.impl.body.stmts = declarations.map ByteOwnerDeclaration.statement := by
      simpa only [implementationEq] using body
    have valueEq : frame.source.impl.body.value = some expression := by
      simpa only [implementationEq] using tail
    have scopeBody : frame.source.impl.body = ⟨frame.source.impl.body.scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩ := by
      cases shape : frame.source.impl.body with
      | mk scope statements value =>
        simp only [shape, Block.stmts] at statementsEq
        simp only [shape, Block.value] at valueEq
        subst statements value
        rfl
    have enough : declarations.length + 2 ≤ fuel + 1 := enoughFuel
    have entryWorld : AcceptedWorld config entryFrame.initialized before [.callChannels activation []] (declaredRootTypes config.module) live [] [] := frameWorld
    have entrySource : AcceptedFrame config accepted entryFrame before (declaredRootTypes config.module) := source
    have framePhase : entryFrame.phase = .implementation config.module.entry := by simpa [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase
    have entryInitialized : entryFrame.initialized = config.module.globals.size := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initializedEntry
    have scopeEq : entryFrame.source.impl.body = ⟨frame.source.impl.body.scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩ := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using scopeBody
    have scopedSource : AcceptedFrame config accepted
        (blockStatementsFrame (implementationBodyFrame config entryFrame) frame.source.impl.body.scope 4095) before
        (declaredRootTypes config.module) := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using source
    have entryOwners : ∀ declaration ∈ declarations,
        (entryFrame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using owners
    have unnamed : ∀ declaration ∈ declarations,
        (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
      intro declaration member
      simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
        Array.toList_empty, List.zipIdx_nil, List.find?_nil]
    have environment : entryFrame.interpretation.environment =
        { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes } := by
      simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq]
    have normal : execStmts (fuel + 1) config entryFrame.interpretation.environment
        (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after := by
      simpa only [implementationEq, body] using outcome
    have completed := acceptedByteEntry_scalarTail_afterNormal fuel config accepted entryFrame before (declaredRootTypes config.module)
      activation activated before after frame.source.impl.body.scope declarations expression [.callChannels activation []]
      (declaredRootTypes config.module) live [] [] entrySource framePhase entryInitialized scopeEq form channels rfl environment
      entryWorld scopedSource entryOwners unnamed enough checkFuel normal
    obtain ⟨tailFrame, tailTypes, tailLive, tailRegions, completed⟩ := completed
    refine ⟨tailFrame, tailTypes, tailLive, tailRegions, ?_⟩
    exact completed

#print axioms acceptedByteEntry_scalarTail_outcome

end Goose.Proofs.ConstructionAcceptedExecution
