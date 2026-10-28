import Goose.Proofs.ConstructionAcceptedMixedModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_scalarLocal_afterRoot (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (descriptor : LocalVar) (expression : Expr) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (root : Goose.Core.RootInst)
    (declared : environment.vars[id]? = some descriptor) (fixed : descriptor.ty.nonfixed = false)
    (resolved : rootOf environment id before = .ok root before) :
    execStmt (fuel + 1) config environment (.letS id expression origin) before =
      (evalValue fuel config environment expression >>= fun value =>
        bindRoot root value >>= fun _ => pure (.normal .unit)) before := by
  simp only [execStmt, declared, fixed, Bool.false_eq_true, ↓reduceIte, bind, resolved]

theorem execStmt_checkedScalarLocal_initializer (fuel checkFuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (descriptor : LocalVar) (expression : Expr) (origin : Goose.Core.OriginId)
    (root : Goose.Core.RootInst) (form : AcceptedBinaryExpression expression)
    (declared : frame.interpretation.environment.vars[id]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (resolved : rootOf frame.interpretation.environment id state = .ok root state)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression descriptor.ty roots typingAfter rootsAfter) :
    let outcome := evalValue fuel config frame.interpretation.environment expression state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after descriptor.ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      execStmt (fuel + 1) config frame.interpretation.environment (.letS id expression origin) state =
        (evalValue fuel config frame.interpretation.environment expression >>= fun value =>
          bindRoot root value >>= fun _ => pure (.normal .unit)) state := by
  have child := ordinaryOperandFrame_accepted accepted frame checkFuel state types source
  have result := evalValue_checked_binary_recursive form fuel config accepted (ordinaryOperandFrame frame checkFuel) state
    ambient types live regions pending world child descriptor.ty roots typingAfter rootsAfter checked
  change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧ _ at result
  refine ⟨result.1, result.2.1, result.2.2.1, ?_, ?_⟩
  · simpa only [result.1] using source
  · exact execStmt_scalarLocal_afterRoot fuel config frame.interpretation.environment id descriptor expression origin state root
      declared fixed resolved

theorem scalarLocal_sourceRoot (checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
    (source : AcceptedFrame config accepted frame state types)
    (position : SourcePosition accepted frame (.statements (.letS id expression origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (scope : Nat) (scopeInst : Nat) (outer : List (Nat × Nat))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outer) :
    ∃ descriptor root,
      frame.typing.variables[id]? = some descriptor ∧
      frame.interpretation.environment.vars[id]? = some descriptor ∧
      id = frame.typingCounter ∧ id = frame.rootCursor.nextVar ∧
      rootOf frame.interpretation.environment id state = .ok root state ∧
      state.objects.lookup root = none ∧ state.objectOrdinals.lookup root = none ∧ types root = none := by
  have head := position.statements_head accepted frame (.letS id expression origin) rest (checkFuel + 1) nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := head.checked accepted _ _
  obtain ⟨descriptor, declared, localScope, typingOrder⟩ := typeStatement_let_descriptor checkFuel frame.typing next id
    expression origin frame.typingCounter typingAfter typed
  have rootOrder := (rpStmt_letS_initializer rooted).1
  have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
    rw [source.compatible.scopes, scopes]; rfl
  have localScope' := localScope.trans (source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes)
  have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]; exact declared
  let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
  have resolved : rootOf frame.interpretation.environment id state = .ok root state := by
    simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing :=
    Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  obtain ⟨absent, ordinal⟩ := source.uninitializedLocals id uninitialized root resolved
  have freshType := source.uninitializedTypes id uninitialized root resolved
  exact ⟨descriptor, root, declared, runtimeDeclared, typingOrder, rootOrder, resolved, absent, ordinal, freshType⟩

theorem reserveRootObject_fresh_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (root : Goose.Core.RootInst)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (fresh : state.objectOrdinals.lookup root = none) :
    let reserved := reserveByteStorage state
    let after := { reserved with objectOrdinals := (root, state.construction.storage.size) ::
      state.objectOrdinals.filter (fun entry => entry.1 != root) }
    reserveRootObject root state = .ok state.construction.storage.size after ∧
      AcceptedWorld config initialized reserved ambient types live regions pending := by
  constructor
  · simp [reserveRootObject, fresh, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set,
      EvalM.get, EvalM.set, setObjectOrdinal, bind, pure, reserveByteStorage]
  · exact reserveByteStorage_world config initialized state ambient types live regions pending world

theorem bindRoot_freshScalar (state : ExecutionState) (root : Goose.Core.RootInst) (value : Value)
    (scalar : (∃ ty number, value = .int ty number) ∨ (∃ boolean, value = .bool boolean))
    (fresh : state.objectOrdinals.lookup root = none) :
    let reserved := reserveByteStorage state
    let after := { reserved with
      objects := (root, value) :: state.objects.filter (fun entry => entry.1 != root)
      objectOrdinals := (root, state.construction.storage.size) :: state.objectOrdinals.filter (fun entry => entry.1 != root) }
    bindRoot root value state = .ok () after := by
  rcases scalar with ⟨ty, number, rfl⟩ | ⟨boolean, rfl⟩ <;>
    simp [bindRoot, fresh, reserveRootObject, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set,
      EvalM.get, EvalM.set, setObjectOrdinal, bindStaticRoot, bind, pure, reserveByteStorage]

#print axioms bindRoot_freshScalar
#print axioms reserveRootObject_fresh_world
#print axioms scalarLocal_sourceRoot
#print axioms execStmt_checkedScalarLocal_initializer
end Goose.Proofs.ConstructionAcceptedExecution
