import Goose.Proofs.ConstructionAcceptedIntegerAssignmentSequence
import Goose.Proofs.ConstructionAcceptedRegisterLetFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execStmts_registerLet_assignments_print_world {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin localId statementOrigin printOrigin : Nat) (assignments : List (Int × Goose.Core.OriginId)) (intTy : Goose.Core.IntTy) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (resultInteger : resultTy = .int intTy) (scope scopeInst : Nat) (outerScopes : List (Nat × Nat))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (mode : parameter.mode = .byValue) (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (position : SourcePosition accepted caller (.statements (.letS localId (.call contextId [.byVal expression] origin) statementOrigin ::
      (localIntegerAssignments localId intTy assignments ++ [.print [.expr (.read (.var localId))] printOrigin]))))
    (localScalar : ∀ localDescriptor, caller.typing.variables[localId]? = some localDescriptor →
      (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool)
    (scopes : caller.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    StatementWorldOutcome config accepted caller.initialized ambient pending
      (execStmts fuel config caller.interpretation.environment
        (.letS localId (.call contextId [.byVal expression] origin) statementOrigin ::
          (localIntegerAssignments localId intTy assignments ++ [.print [.expr (.read (.var localId))] printOrigin])) state) := by
  cases fuel with
  | zero =>
    simp only [execStmts, timeout, EvalM.stop, StatementWorldOutcome]
    exact ⟨ambient, types, live, regions, world⟩
  | succ fuel =>
    obtain ⟨_, _, _, typed, _⟩ := position.checked accepted caller _
    cases nesting : caller.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ headFuel =>
      let headFrame := { caller with typingFuel := headFuel }
      have headPosition := position.statements_head accepted caller
        (.letS localId (.call contextId [.byVal expression] origin) statementOrigin)
        (localIntegerAssignments localId intTy assignments ++ [.print [.expr (.read (.var localId))] printOrigin]) headFuel nesting
      have headSource := callerSource.withTypingFuel headFuel
      obtain ⟨checkFuel, checkNesting⟩ := headPosition.registerLet_fuel headFrame localId statementOrigin contextId origin expression context helper
        headSource.compatible contextAt helperAt
      have first := mixedLocalRegisterParameter_position_letAllFuel shape fuel checkFuel config accepted headFrame state ambient types live regions pending
        contextId origin localId statementOrigin context helper parameter descriptor resultTy resultExpression scope scopeInst outerScopes
        contextAt helperAt parameters results mode resultScalar declared scalar callerInitialized world headSource bounded checkNesting headPosition
        localScalar scopes form tail resultShape owners scalarOwners depth outer
      cases head : execStmt fuel config caller.interpretation.environment
          (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state with
      | escape target carriers after | jump target kind after => simp only [headFrame, head] at first
      | stop reason after =>
        simp only [headFrame, head] at first
        obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩ := first
        simp only [execStmts, bind, head, StatementWorldOutcome]
        exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, callerInitialized.symm ▸ finalWorld⟩
      | ok flow after =>
        simp only [headFrame, head] at first
        obtain ⟨normal, nextTypes, nextLive, nextRegions, nextWorld, nextSource⟩ := first
        subst flow
        let nextFrame := advanceLocalFrame headFrame localId
        let root := Goose.Core.RootInst.local caller.interpretation.environment.act scopeInst localId
        let registered := registerRootType nextTypes root resultTy
        let nextLive' := fun other => other = root ∨ nextLive other
        have visible : localId ∈ nextFrame.typing.visible := by simp [nextFrame, advanceLocalFrame]
        obtain ⟨typingNext, typingAfterStmt, rootAfter, typed, rooted⟩ := headPosition.checked accepted headFrame _
        have contextAt' : headFrame.typing.module.contexts[contextId]? = some context := by rw [headSource.compatible.module]; exact contextAt
        have helperAt' : headFrame.typing.module.impls[context.impl]? = some helper := by rw [headSource.compatible.module]; exact helperAt
        obtain ⟨localDescriptor, localDeclared, order, resultType⟩ := typeStatement_registerCall_result (checkFuel + 2)
          headFrame.typing typingNext localId contextId origin statementOrigin [.byVal expression] headFrame.typingCounter typingAfterStmt
          context helper resultTy contextAt' helperAt' results resultScalar localScalar (by simpa [checkNesting] using typed)
        have nextLocalType : ∀ descriptor, nextFrame.typing.variables[localId]? = some descriptor → descriptor.ty = .int intTy := by
          intro descriptor found
          have found' : headFrame.typing.variables[localId]? = some descriptor := by simpa [nextFrame, advanceLocalFrame] using found
          have same : descriptor = localDescriptor := Option.some.inj (found'.symm.trans localDeclared)
          subst descriptor
          exact resultType.trans resultInteger
        have nextBounded : GlobalEffectTargetsBounded nextFrame.rootCursor.eff config.module.globals.size := by
          simpa [nextFrame, advanceLocalFrame, headFrame] using bounded
        have result := execStmts_integerAssignments_print_world assignments fuel config accepted nextFrame after ambient registered nextLive' nextRegions pending
          localId intTy printOrigin nextWorld nextSource visible callerInitialized nextBounded nextLocalType
        simpa only [execStmts, bind, head, nextFrame, advanceLocalFrame, headFrame] using result

#print axioms execStmts_registerLet_assignments_print_world
end Goose.Proofs.ConstructionAcceptedExecution
