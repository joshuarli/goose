import Goose.Proofs.ConstructionAcceptedCallLocalSuffix
import Goose.Proofs.ConstructionAcceptedScalarPrefixCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive CallLocalStatements (config : EvalConfig) (ty : Ty) : List Stmt → Prop
  | nil : CallLocalStatements config ty []
  | scalar (id : Nat) (expression : Expr) (origin : Nat) (rest : List Stmt)
      (expressionForm : AcceptedBinaryExpression expression) (tail : CallLocalStatements config ty rest) :
      CallLocalStatements config ty (.letS id expression origin :: rest)
  | call (id target callOrigin statementOrigin : Nat) (rest : List Stmt) (context : Context) (callee : Impl)
      (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
      (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
      (tail : CallLocalStatements config ty rest) :
      CallLocalStatements config ty (.letS id (.call target [] callOrigin) statementOrigin :: rest)

theorem execStmts_callLocals (config : EvalConfig) (ty : Ty) {statements : List Stmt} (form : CallLocalStatements config ty statements)
    (accepted : AcceptedModule config) (context frontier budget scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat)) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (inner : ∀ callFuel, callFuel < budget → ∀ (caller : ConstructionSourceFrame) (before : ExecutionState)
        (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
        (target : Nat) (calleeContext : Context) (callee : Impl) (origin : Nat)
        (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedWorld config caller.initialized before ambient types live regions pending →
      AcceptedFrame config accepted caller before types →
      config.module.contexts[target]? = some calleeContext → config.module.impls[calleeContext.impl]? = some callee →
      callee.params = #[] → callee.results = #[⟨ty, .register, none⟩] →
      CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config caller.interpretation.environment target [] [.register ty] origin before
        RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∀ fuel, fuel ≤ budget → ∀ (frame : ConstructionSourceFrame) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      frontier ≤ frame.interpretation.environment.act → frontier ≤ before.nextAct →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes →
      SourcePosition accepted frame (.statements statements) →
      (∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) →
      (∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
        frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
        let outcome := execStmts fuel config frame.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧ before.nextAct ≤ after.nextAct ∧
        before.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier before after types nextTypes ∧
        (match outcome with
         | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧ ScalarLocalReplay frame next statements
         | .stop .. => True | .escape .. | .jump .. => False) := by
  induction form with
  | nil =>
    intro fuel bound frame before ambient types live frontierAct frontierClock world source phase scopes position available scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        EarlierCallerObservations.refl frontier before types, trivial⟩
    | succ fuel =>
      simp only [execStmts, pure, Goose.Proofs.Exit.stepState]
      obtain ⟨_, _, _, typed, _⟩ := position.checked accepted frame _
      cases depth : frame.typingFuel with
      | zero => rw [depth] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ n =>
        have replay : ScalarLocalReplay frame frame [] := by simp [ScalarLocalReplay, depth, typeStatements, rpStmts, pure, StateT.pure, Except.pure]
        exact ⟨frame, types, live, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
          EarlierCallerObservations.refl frontier before types, rfl, trivial, position, replay⟩
  | scalar id expression origin rest expressionForm tail ih =>
    intro fuel bound frame before ambient types live frontierAct frontierClock world source phase scopes position available scalar
    let invariant : ConstructionSourceFrame → Prop := fun current =>
      current.source.impl.vars = frame.source.impl.vars ∧ current.interpretation.environment.scopes = frame.interpretation.environment.scopes
    have advance : ∀ current id fuel roots, invariant current →
        invariant { advanceLocalFrame { current with typingFuel := fuel } id with rootCursor := roots } := by
      intro current id fuel roots valid
      simpa [invariant, advanceLocalFrame] using valid
    have single : ScalarLocalStatements [.letS id expression origin] := .cons id expression origin [] expressionForm .nil
    have oneScalar : ∀ (localId : Nat) (localExpression : Expr) (localOrigin : Nat), Stmt.letS localId localExpression localOrigin ∈ [Stmt.letS id expression origin] → ∀ (descriptor : LocalVar),
        frame.source.impl.vars[localId]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
      intro localId localExpression localOrigin member descriptor declared
      have same : Stmt.letS localId localExpression localOrigin = .letS id expression origin := by simpa using member
      exact scalar localId localExpression localOrigin (List.mem_cons.mpr (Or.inl same)) descriptor declared
    exact execStmts_scalarPrefix_fromSuffix single rest config accepted context frontier budget regions pending (fun _ => True) invariant advance (by
      intro n nBound nextFrame middle nextAmbient nextTypes nextLive _ valid nextAct nextClock nextWorld nextSource nextPhase nextPosition nextAvailable
      have nextScopes : nextFrame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes := by rw [valid.2]; exact scopes
      have nextScalar : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
          nextFrame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
        intro id expression origin member descriptor declared
        apply scalar id expression origin (List.mem_cons_of_mem _ member) descriptor
        rw [valid.1] at declared
        exact declared
      exact ih n nBound nextFrame middle nextAmbient nextTypes nextLive nextAct nextClock nextWorld nextSource nextPhase nextScopes nextPosition nextAvailable nextScalar)
      fuel bound frame before ambient types live trivial ⟨rfl, rfl⟩ frontierAct frontierClock world source phase position available oneScalar
  | call id target callOrigin statementOrigin rest calleeContext callee contextAt calleeAt parameters results tail ih =>
    intro fuel bound frame before ambient types live frontierAct frontierClock world source phase scopes position available scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        EarlierCallerObservations.refl frontier before types, trivial⟩
    | succ fuel =>
      have depth := position.zeroArgumentCallLocal_nesting frame before types id target callOrigin statementOrigin rest
        calleeContext callee ty source contextAt calleeAt parameters results scalarTy
      let checkFuel := frame.typingFuel - 3
      have nesting : frame.typingFuel = (checkFuel + 1) + 2 := by simp [checkFuel]; omega
      have localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
          (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
        intro descriptor declared
        apply scalar id (.call target [] callOrigin) statementOrigin (by simp) descriptor
        rw [source.compatible.sourceVariables]; exact declared
      have headPosition := position.statements_head accepted frame (.letS id (.call target [] callOrigin) statementOrigin) rest
        (checkFuel + 2) (by omega)
      obtain ⟨_, _, allRoots, _, rootedAll⟩ := position.checked accepted frame _
      obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
      have headAvailable : ∀ after, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor =
          .ok ((), after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff := by
        intro after rooted
        have same : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
        subst after
        have included := rpStmts_effectTargetsIncluded tailRooted
        intro target member global rooted
        exact available allRoots rootedAll target (included member) global rooted
      have headSource := source.withTypingFuel (checkFuel + 2)
      obtain ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameTy, initialSource, checked⟩ :=
        checked_recursiveRegisterCall_initializer { frame with typingFuel := checkFuel + 2 } before types id statementOrigin target callOrigin checkFuel
          calleeContext callee ty headSource contextAt calleeAt results scalarTy localScalar rfl headPosition headAvailable
      apply execStmts_callLocal_fromSuffix fuel checkFuel config accepted frame before ambient types live regions pending
        id statementOrigin target callOrigin rest calleeContext callee ty scope scopeInst outerScopes world source contextAt calleeAt parameters results
        scalarTy localScalar nesting position available scopes frontier frontierClock frontierAct (by
          intro evalFuel callFuel first second
          exact inner callFuel (by omega) (letInitializerFrame { frame with typingFuel := checkFuel + 2 } id (checkFuel + 1))
            before ambient types live target calleeContext callee callOrigin roots typingAfter rootsAfter
            world initialSource contextAt calleeAt parameters results checked)
      intro rootsAfter middle nextTypes nextLive nextFrame middleWorld middleSource middlePosition remainingAvailable
      have nextScopes : nextFrame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes := by
        simpa [nextFrame, advanceLocalFrame] using scopes
      have nextScalar : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
          nextFrame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
        intro id expression origin member descriptor found
        apply scalar id expression origin (List.mem_cons_of_mem _ member) descriptor
        simpa [nextFrame, advanceLocalFrame] using found
      have nextAct : frontier ≤ nextFrame.interpretation.environment.act := by simpa [nextFrame, advanceLocalFrame] using frontierAct
      have nextClock : frontier ≤ middle.nextAct := by
        have liveAct := middleSource.frontier.1
        exact Nat.le_trans nextAct (Nat.le_of_lt liveAct)
      exact ih fuel (by omega) nextFrame middle ambient nextTypes nextLive nextAct nextClock middleWorld middleSource
        (by simpa [nextFrame, advanceLocalFrame] using phase) nextScopes middlePosition remainingAvailable nextScalar

#print axioms execStmts_callLocals
end Goose.Proofs.ConstructionAcceptedExecution
