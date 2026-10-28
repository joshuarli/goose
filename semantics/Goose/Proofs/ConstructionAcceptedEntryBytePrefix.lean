import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedZeroGlobalEntryBytePrefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (rest : List Stmt) (original : Context) (implementation : Impl)
    (noGlobals : config.module.globals.size = 0)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (bodyPrefix : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement ++ rest)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (runFuel : declarations.length + 2 ≤ fuel) (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation)
      (completed remaining : List ByteOwnerDeclaration) (remainingFuel : Nat) (next : ConstructionSourceFrame)
      (middle : ExecutionState) (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let initial := ExecutionState.initial
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initial with nextAct := initial.nextAct + 1, activations := activation :: initial.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts after
      runModule (fuel + 3) config initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initial ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initial =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧
      entryFrame.interpretation.environment =
        { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes } ∧
      declarations = completed ++ remaining ∧ remainingFuel + completed.length = fuel ∧
      next.interpretation = entryFrame.interpretation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized middle [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next middle types ∧
      SourcePosition accepted next (.statements (remaining.map ByteOwnerDeclaration.statement ++ rest)) ∧
      ((remaining = [] ∧ execStmts remainingFuel config next.interpretation.environment rest middle = outcome) ∨
       (∃ declaration tail, remaining = declaration :: tail ∧
         execStmt (remainingFuel - 1) config next.interpretation.environment declaration.statement middle = outcome)) := by
  obtain ⟨frame, activation, moduleStep, callStep, environmentEq, world, source, position, phase, results⟩ :=
    acceptedZeroGlobalRunEntry fuel config accepted noGlobals
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1, activations := activation :: ExecutionState.initial.activations }
  let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have position' : SourcePosition accepted entryFrame (.statements (declarations.map ByteOwnerDeclaration.statement ++ rest)) := by
    rw [← bodyPrefix, ← implementationEq]
    exact position
  have owners' : ∀ declaration ∈ declarations,
      (entryFrame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using owners declaration member
  have unnamed : ∀ declaration ∈ declarations,
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts after
  have executed : execStmts fuel config entryFrame.interpretation.environment
      (declarations.map ByteOwnerDeclaration.statement ++ rest) after = outcome := by
    simp only [outcome, ← bodyPrefix, ← implementationEq]
  obtain ⟨completed, remaining, remainingFuel, next, middle, types, live, regions,
    decomposition, fuelEq, interpretationEq, initializedEq, extended, nextWorld, nextSource, nextPosition, residual⟩ :=
    execStmts_byteOwners_prefix declarations fuel 4094 config accepted entryFrame config.module.entry rest after outcome
      [.callChannels activation []] (declaredRootTypes config.module) (fun _ => False) [] [] runFuel checkFuel rfl
      world source (by simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase)
      position' owners' unnamed executed
  have bodyEnvironment : entryFrame.interpretation.environment =
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes } := by
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq]
  exact ⟨frame, activation, completed, remaining, remainingFuel, next, middle, types, live, regions,
    moduleStep, callStep, implementationEq, environmentEq, bodyEnvironment, decomposition, fuelEq, interpretationEq, initializedEq,
    extended, nextWorld, nextSource, nextPosition, residual⟩

#print axioms acceptedZeroGlobalEntryBytePrefix

end Goose.Proofs.ConstructionAcceptedExecution
