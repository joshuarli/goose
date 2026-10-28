import Goose.Proofs.ConstructionAcceptedScalarGlobalExpression
import Goose.Proofs.ConstructionAcceptedBinaryTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem typeExpr_if_condition (fuel : Nat) (environment : TypingEnv) (condition : Expr)
    (yes no : Block) (origin : Nat) (before after : Nat) (types : List Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition yes no origin) before = .ok (types, after)) :
    ∃ middle, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], middle) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  cases first : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } condition before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨conditionTypes, middle⟩ := result
    simp only [first, Except.bind] at checked
    cases conditionTypes with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons conditionType tail =>
      cases tail with
      | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        cases conditionType <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
        case bool => exact ⟨middle, rfl⟩

theorem rpExpr_if_condition (environment : PEnv) (condition : Expr) (yes no : Block) (origin : Nat)
    (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.ifE condition yes no origin) before = .ok (roots, after)) :
    ∃ conditionRoots middle, rpExpr environment condition before = .ok (conditionRoots, middle) ∧
      EffectTargetsIncluded middle.eff after.eff := by
  change (Except.bind (rpExpr environment condition before) _) = .ok (roots, after) at checked
  cases first : rpExpr environment condition before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨conditionRoots, middle⟩ := result
    simp only [first, Except.bind] at checked
    change (Except.bind (rpBlockValue environment [] yes middle) _) = _ at checked
    cases second : rpBlockValue environment [] yes middle with
    | error failure => simp only [second, Except.bind] at checked; cases checked
    | ok result =>
      obtain ⟨yesResult, yesAfter⟩ := result
      simp only [second, Except.bind] at checked
      change (Except.bind (rpBlockValue environment [] no yesAfter) _) = _ at checked
      cases third : rpBlockValue environment [] no yesAfter with
      | error failure => simp only [third, Except.bind] at checked; cases checked
      | ok result =>
        obtain ⟨noResult, noAfter⟩ := result
        simp only [third, Except.bind] at checked
        change Except.ok (_, noAfter) = Except.ok (roots, after) at checked
        cases checked
        exact ⟨conditionRoots, middle, rfl,
          EffectTargetsIncluded.trans (rpBlockValue_effectTargetsIncluded second) (rpBlockValue_effectTargetsIncluded third)⟩

theorem checkedValue_if_condition (frame : ConstructionSourceFrame) (fuel : Nat)
    (condition : Expr) (yes no : Block) (origin : Nat) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.ifE condition yes no origin) ty roots typingAfter rootsAfter) :
    ∃ conditionRoots typingMiddle rootsMiddle,
      CheckedValue (ordinaryOperandFrame frame fuel) condition .bool conditionRoots typingMiddle rootsMiddle := by
  have typed := checked.typing
  rw [fuelAt] at typed
  obtain ⟨typingMiddle, conditionTyped⟩ := typeExpr_if_condition fuel frame.typing condition yes no origin
    frame.typingCounter typingAfter [ty] typed
  obtain ⟨conditionRoots, rootsMiddle, conditionRooted, included⟩ :=
    rpExpr_if_condition frame.source condition yes no origin frame.rootCursor rootsAfter roots checked.provenance
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsMiddle.eff := by
    intro target member global rooted
    exact checked.available target (included member) global rooted
  exact ⟨conditionRoots, typingMiddle, rootsMiddle, conditionTyped, conditionRooted, available⟩

theorem accepted_globalConditional_condition (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (condition : Expr) (yes no : Block) (origin : Nat)
    (shape : descriptor.init = .ifE condition yes no origin) (form : AcceptedBinaryExpression condition) :
    ∃ names conditionRoots typingMiddle rootsMiddle,
      let frame := ordinaryOperandFrame (scalarGlobalInitializerFrame config id before.nextAct names) 4095
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] ∧
      AcceptedFrame config accepted frame activated types ∧
      CheckedValue frame condition .bool conditionRoots typingMiddle rootsMiddle := by
  obtain ⟨names, activeWorld, frameSource, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed rooted
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  obtain ⟨typingMiddle, conditionTyped⟩ := typeExpr_if_condition 4095 frame.typing condition yes no origin 0 typingAfter [ty] typed
  obtain ⟨conditionRoots, rootsMiddle, conditionRooted, included⟩ :=
    rpExpr_if_condition frame.source condition yes no origin frame.rootCursor rootsAfter roots rooted
  have initial : GlobalEffectTargetsBounded frame.rootCursor.eff id := by
    simp [frame, scalarGlobalInitializerFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have effects := recursiveScalar_effects_bounded form 4095
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } frame.source id 0 typingMiddle
      frame.rootCursor rootsMiddle [.bool] conditionRoots (by simp [frame, scalarGlobalInitializerFrame]) initial conditionTyped conditionRooted
  have available : GlobalEffectsAvailable frame.interpretation id rootsMiddle.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact effects other member
    | param parameter => exact instantiated.1.elim
  exact ⟨names, conditionRoots, typingMiddle, rootsMiddle, activeWorld,
    ordinaryOperandFrame_accepted accepted frame 4095 _ types frameSource, conditionTyped, conditionRooted, available⟩

theorem accepted_globalConditional_condition_evaluates (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (condition : Expr) (yes no : Block) (origin : Nat)
    (shape : descriptor.init = .ifE condition yes no origin) (form : AcceptedBinaryExpression condition) :
    let activated := { before with nextAct := before.nextAct + 1 }
    let outcome := evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated
    Goose.Proofs.Exit.stepState outcome = activated ∧
    AcceptedWorld config id (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
    (match outcome with | .ok (.bool _) _ | .stop _ _ => True | _ => False) := by
  obtain ⟨names, roots, typingMiddle, rootsMiddle, activeWorld, frameSource, checked⟩ :=
    accepted_globalConditional_condition config accepted id descriptor before ambient types live world clear present condition yes no origin shape form
  let frame := ordinaryOperandFrame (scalarGlobalInitializerFrame config id before.nextAct names) 4095
  let activated := { before with nextAct := before.nextAct + 1 }
  have evaluated := evalValue_checked_binary_recursive form fuel config accepted frame activated ambient types live [] []
    activeWorld frameSource .bool roots typingMiddle rootsMiddle checked
  change Goose.Proofs.Exit.stepState (evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated) = activated ∧ _ at evaluated
  refine ⟨evaluated.1, evaluated.2.2.1, ?_⟩
  cases execution : evalValue fuel config ⟨0, before.nextAct, #[], [], []⟩ condition activated with
  | stop reason after => trivial
  | escape address carriers after =>
    exact ((evalValue_scalar_controlFree form fuel config ⟨0, before.nextAct, #[], [], []⟩).1 activated address carriers after execution).elim
  | jump target kind after =>
    exact ((evalValue_scalar_controlFree form fuel config ⟨0, before.nextAct, #[], [], []⟩).2 activated target kind after execution).elim
  | ok value after =>
    have valid := evaluated.2.1 value after execution
    cases value <;> cases valid.represented <;> simp_all [Ty.nonfixed]

#print axioms accepted_globalConditional_condition_evaluates
#print axioms accepted_globalConditional_condition
#print axioms checkedValue_if_condition
#print axioms rpExpr_if_condition
#print axioms typeExpr_if_condition
end Goose.Proofs.ConstructionAcceptedExecution
