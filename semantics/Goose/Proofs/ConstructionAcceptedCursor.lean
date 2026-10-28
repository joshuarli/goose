import Goose.Proofs.ConstructionAcceptedValues

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private theorem except_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

def ordinaryOperandFrame (frame : ConstructionSourceFrame) (fuel : Nat) : ConstructionSourceFrame :=
  { frame with
    typingFuel := fuel
    typing := { frame.typing with use := .ordinary, request := .value, resultRequests := [] } }

theorem ordinaryOperandFrame_compatible {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel : Nat) (valid : SourceFrameCompatible accepted frame) :
    SourceFrameCompatible accepted (ordinaryOperandFrame frame fuel) := by
  exact ⟨valid.module, valid.rootModule, valid.variables, valid.sourceVariables, valid.scopes,
    valid.globalCount, valid.globals, valid.initialized, valid.declarations, valid.typingBound,
    valid.visible, valid.initializing, valid.currentScope, valid.origin⟩

theorem ordinaryOperandFrame_accepted {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel : Nat) (state : ExecutionState) (types : RootTypes)
    (valid : AcceptedFrame config accepted frame state types) :
    AcceptedFrame config accepted (ordinaryOperandFrame frame fuel) state types :=
  ⟨ordinaryOperandFrame_compatible accepted frame fuel valid.compatible,
    valid.frontier, valid.scopeFrontier, valid.aliases, valid.locals, valid.localTypes, valid.uninitializedLocals, valid.futureGlobals,
    valid.direct, valid.contents⟩

theorem rpExpr_not_operand (environment : PEnv) (expression : Expr) (before after : RState)
    (roots : List RootRef) (checked : (rpExpr environment (.not expression)).run before = .ok (roots, after)) :
    roots = [] ∧ ∃ operandRoots, (rpExpr environment expression).run before = .ok (operandRoots, after) := by
  change (Except.bind (rpExpr environment expression before) fun result =>
    .ok ([], result.2)) = .ok (roots, after) at checked
  cases operand : rpExpr environment expression before with
  | error failure => simp only [operand, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨operandRoots, next⟩ := result
    simp only [operand, Except.bind] at checked
    cases checked
    exact ⟨rfl, operandRoots, operand⟩

theorem typeExpr_not_operand (fuel : Nat) (environment : TypingEnv) (expression : Expr)
    (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.not expression) before = .ok ([ty], after)) :
    ty = .bool ∧ typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok ([.bool], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before) _) = .ok ([ty], after) at checked
  generalize operand : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = result at checked
  cases result with
  | error failure => simp only [Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨types, next⟩ := result
    cases types with
    | nil =>
      change Except.error _ = Except.ok _ at checked
      cases checked
    | cons head tail =>
      cases tail with
      | cons second rest =>
        change Except.error _ = Except.ok _ at checked
        cases checked
      | nil =>
        cases head <;> first
        | change Except.error _ = Except.ok _ at checked
          cases checked
        | change Except.ok ([Ty.bool], next) = Except.ok ([ty], after) at checked
          cases checked
          exact ⟨rfl, rfl⟩

theorem checkedValue_not_operand (frame : ConstructionSourceFrame) (fuel : Nat)
    (expression : Expr) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.not expression) ty roots typingAfter rootsAfter) :
    ty = .bool ∧ roots = [] ∧ ∃ operandRoots,
      CheckedValue (ordinaryOperandFrame frame fuel) expression .bool operandRoots typingAfter rootsAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨type, operandTyping⟩ := typeExpr_not_operand fuel frame.typing expression
    frame.typingCounter typingAfter ty typing
  obtain ⟨empty, operandRoots, operandProvenance⟩ := rpExpr_not_operand frame.source expression
    frame.rootCursor rootsAfter roots checked.provenance
  exact ⟨type, empty, operandRoots, operandTyping, operandProvenance, checked.available⟩

theorem evalValue_not_of_operand (fuel : Nat) (config : EvalConfig) (frame : ConstructionSourceFrame)
    (types : RootTypes) (before after : ExecutionState) (expression : Expr) (roots : List RootRef)
    (value : Value)
    (evaluated : evalValue fuel config frame.interpretation.environment expression before = .ok value after)
    (accepted : AcceptedValue config.layout types frame.interpretation after .bool roots value) :
    ∃ result, evalValue (fuel + 1) config frame.interpretation.environment (.not expression) before =
      .ok (.bool result) after ∧
      AcceptedValue config.layout types frame.interpretation after .bool [] (.bool result) := by
  cases represented : accepted.represented with
  | boolean value =>
    exact ⟨!value, by simp only [evalValue, evaluated, bind, expectBool, pure],
      acceptedValue_boolean config.layout types frame.interpretation after (!value)⟩
  | stored => contradiction

theorem checkedValue_globalRead_available (frame : ConstructionSourceFrame) (id : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.read (.global id)) ty roots typingAfter rootsAfter) :
    id < frame.initialized := by
  have provenance := checked.provenance
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
      result.toOption.map (fun pair => pair.2.eff.reads)) provenance
  change some (addTargets frame.rootCursor.eff.reads [.global id]) = some rootsAfter.eff.reads at extracted
  have reads := (Option.some.inj extracted).symm
  apply checked.available (.global id) _ id rfl
  apply List.mem_append_left
  rw [reads]
  simp only [addTargets, List.foldl_cons, List.foldl_nil]
  split <;> simp_all

theorem typeExpr_globalRead_type (fuel : Nat) (environment : TypingEnv) (id : Nat)
    (descriptor : Global) (declared : environment.module.globals[id]? = some descriptor)
    (before after : Nat) (ty : Ty)
    (checked : typeExpr fuel environment (.read (.global id)) before = .ok ([ty], after)) :
    ty = descriptor.ty := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at checked; cases checked
  | succ fuel =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      by_cases available : id ≥ environment.globalLimit
      · simp only [typeExpr, typePlace, available, ↓reduceIte, bind, StateT.bind] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      · simp only [typeExpr, typePlace, available, ↓reduceIte, declared, bind, StateT.bind] at checked
        simp only [pure, StateT.pure, Except.bind] at checked
        obtain ⟨result, _, returned⟩ := except_bind_success _ _ _ checked
        cases returned
        rfl

theorem evalValue_checkedGlobalRead (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types liveRoots regions pending)
    (compatible : SourceFrameCompatible accepted frame) (id : Nat) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.read (.global id)) ty roots typingAfter rootsAfter) :
    ∃ value, evalValue (fuel + 2) config frame.interpretation.environment (.read (.global id)) state =
      .ok value state ∧ Goose.Proofs.ConstructionRepresentation.ValueRepresentation ty value ∧
      PointerTypedValue types ty value ∧
      Goose.Proofs.ConstructionRepresentation.ValueStorageBacked config.layout state value := by
  have available := checkedValue_globalRead_available frame id ty roots typingAfter rootsAfter checked
  obtain ⟨descriptor, value, declared, evaluated, represented, pointers, backed⟩ :=
    evalValue_initializedGlobal fuel config frame.interpretation frame.initialized state ambient types liveRoots
      regions pending world id available
  have sourceDeclared : frame.typing.module.globals[id]? = some descriptor := by
    rw [compatible.module]
    exact declared
  have type := typeExpr_globalRead_type frame.typingFuel frame.typing id descriptor sourceDeclared
    frame.typingCounter typingAfter ty checked.typing
  subst ty
  exact ⟨value, evaluated, represented, pointers, backed⟩

theorem typeExpr_globalReference_type (fuel : Nat) (environment : TypingEnv) (id : Nat)
    (descriptor : Global) (declared : environment.module.globals[id]? = some descriptor)
    (mutability : Goose.Core.Mutability) (before after : Nat) (ty : Ty)
    (checked : typeExpr fuel environment (.ref mutability (.global id)) before = .ok ([ty], after)) :
    ty = .ref mutability descriptor.ty := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at checked; cases checked
  | succ fuel =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      by_cases available : id ≥ environment.globalLimit
      · simp only [typeExpr, typePlace, available, ↓reduceIte, bind, StateT.bind] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      · simp only [typeExpr, typePlace, available, ↓reduceIte, declared, bind, StateT.bind,
          pure, StateT.pure, Except.bind] at checked
        obtain ⟨_, _, checked⟩ := except_bind_success _ _ _ checked
        obtain ⟨_, _, checked⟩ := except_bind_success _ _ _ checked
        cases checked
        rfl

theorem evalValue_checkedGlobalReference (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types liveRoots regions pending)
    (compatible : SourceFrameCompatible accepted frame) (id : Nat) (descriptor : Global)
    (declared : config.module.globals[id]? = some descriptor) (mutability : Goose.Core.Mutability)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.ref mutability (.global id)) ty roots typingAfter rootsAfter) :
    evalValue (fuel + 2) config frame.interpretation.environment (.ref mutability (.global id)) state =
      .ok (.ref ⟨.global id, []⟩) state ∧
      AcceptedValue config.layout types frame.interpretation state ty roots (.ref ⟨.global id, []⟩) := by
  have sourceDeclared : frame.typing.module.globals[id]? = some descriptor := by
    rw [compatible.module]
    exact declared
  have type := typeExpr_globalReference_type frame.typingFuel frame.typing id descriptor sourceDeclared
    mutability frame.typingCounter typingAfter ty checked.typing
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map Prod.fst)
    checked.provenance
  change some [.global id] = some roots at extracted
  have rootList := (Option.some.inj extracted).symm
  subst ty roots
  exact evalValue_globalReference fuel config frame.interpretation frame.initialized state ambient types liveRoots
    regions pending world compatible.globalCount id descriptor declared mutability

theorem evalValue_checkedGlobalRead_accepted (fuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (liveRoots : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types liveRoots regions pending)
    (compatible : SourceFrameCompatible accepted frame) (id : Nat) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.read (.global id)) ty roots typingAfter rootsAfter) :
    ∃ value, evalValue (fuel + 2) config frame.interpretation.environment (.read (.global id)) state =
      .ok value state ∧ AcceptedValue config.layout types frame.interpretation state ty roots value := by
  obtain ⟨value, evaluated, represented, pointers, backed⟩ := evalValue_checkedGlobalRead fuel config accepted frame
    state ambient types liveRoots regions pending world compatible id ty roots typingAfter rootsAfter checked
  have available := checkedValue_globalRead_available frame id ty roots typingAfter rootsAfter checked
  obtain ⟨descriptor, _, declared, _, _⟩ := world.globals.2 id available
  have sourceDeclared : frame.typing.module.globals[id]? = some descriptor := by
    rw [compatible.module]
    exact declared
  have type := typeExpr_globalRead_type frame.typingFuel frame.typing id descriptor sourceDeclared
    frame.typingCounter typingAfter ty checked.typing
  have storage : ty.storageType = true := by
    rw [type]
    exact validated_global_storageType config.module id descriptor accepted.accepted declared
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) => result.toOption.map Prod.fst)
    checked.provenance
  change some [] = some roots at extracted
  have rootList := (Option.some.inj extracted).symm
  subst roots
  refine ⟨value, evaluated, represented, pointers, backed, ?_⟩
  intro location reference
  cases reference <;> cases represented <;> cases storage

#print axioms rpExpr_not_operand
#print axioms typeExpr_not_operand
#print axioms checkedValue_not_operand
#print axioms evalValue_not_of_operand
#print axioms checkedValue_globalRead_available
#print axioms typeExpr_globalRead_type
#print axioms evalValue_checkedGlobalRead
#print axioms evalValue_checkedGlobalReference
#print axioms evalValue_checkedGlobalRead_accepted

end Goose.Proofs.ConstructionAcceptedExecution
