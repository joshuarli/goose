import Goose.Proofs.ConstructionAcceptedScalarConditional

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

inductive ScalarConditionalGlobal (descriptor : Global) : Prop
  | integer (condition : Bool) (yesScope noScope : Nat) (intTy : Goose.Core.IntTy) (yes no : Int)
      (origin : Goose.Core.OriginId) (type : descriptor.ty = .int intTy)
      (initializer : descriptor.init = .ifE (.bool condition) ⟨yesScope, [], some (.lit intTy yes)⟩
        ⟨noScope, [], some (.lit intTy no)⟩ origin) : ScalarConditionalGlobal descriptor
  | boolean (condition : Bool) (yesScope noScope : Nat) (yes no : Bool)
      (origin : Goose.Core.OriginId) (type : descriptor.ty = .bool)
      (initializer : descriptor.init = .ifE (.bool condition) ⟨yesScope, [], some (.bool yes)⟩
        ⟨noScope, [], some (.bool no)⟩ origin) : ScalarConditionalGlobal descriptor

private theorem initGlobals_scalarConditional_core (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (condition : Bool) (yesScope noScope : Nat) (yes no : Expr) (yesValue noValue : Value)
    (origin : Goose.Core.OriginId) (yesLiteral : ScalarLiteral yes yesValue) (noLiteral : ScalarLiteral no noValue)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor)
    (initializer : descriptor.init = .ifE (.bool condition) ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (fixed : descriptor.ty.nonfixed = false)
    (yesRepresentation : ValueRepresentation descriptor.ty yesValue) (noRepresentation : ValueRepresentation descriptor.ty noValue)
    (yesPointers : PointerTypedValue types descriptor.ty yesValue) (noPointers : PointerTypedValue types descriptor.ty noValue) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed = initialized ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  have activeClear := clear.freshAct
  obtain ⟨nextLive, evaluatedWorld, flow⟩ := evalValue_scalarLiteralIf_world fuel config environment condition yesScope noScope
    yes no yesValue noValue yesLiteral noLiteral origin initialized activated ambient types live [] [] activeWorld
  have evaluatedClear := evalValue_scalarLiteralIf_futureGlobals fuel config environment condition yesScope noScope yes no yesValue noValue
    yesLiteral noLiteral origin initialized activated rfl activeClear
  cases execution : evalValue fuel config environment (.ifE (.bool condition) ⟨yesScope, [], some yes⟩
      ⟨noScope, [], some no⟩ origin) activated with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at evaluatedWorld evaluatedClear flow
    have stopped : initGlobals fuel config [initialized] before = .stop reason after := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, initializer, execution, environment, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, nextLive, by omega, by omega, evaluatedWorld, rfl, evaluatedClear⟩
  | escape address carriers after | jump target kind after => simp only [execution] at flow
  | ok value evaluated =>
    simp only [execution, Goose.Proofs.Exit.stepState] at evaluatedWorld evaluatedClear flow
    subst value
    have represented : ValueRepresentation descriptor.ty (if condition then yesValue else noValue) := by
      cases condition <;> simp_all
    have pointers : PointerTypedValue types descriptor.ty (if condition then yesValue else noValue) := by
      cases condition <;> simp_all
    have scalarValue : (∃ intTy number, (if condition then yesValue else noValue) = .int intTy number) ∨
        ∃ boolean, (if condition then yesValue else noValue) = .bool boolean := by
      cases condition <;> cases yesLiteral <;> cases noLiteral <;> simp
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config initialized evaluated ambient types nextLive descriptor
      (if condition then yesValue else noValue) evaluatedWorld declared scalarValue represented pointers
    have done : initGlobals fuel config [initialized] before = .ok () after := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, initializer, execution, bound,
        environment, activated]
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨initialized + 1, (fun root => root = .global initialized ∨ nextLive root), by omega, by omega,
      afterWorld, rfl, evaluatedClear.bindGlobal (if condition then yesValue else noValue) bound⟩

theorem initGlobals_scalarConditional_single (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before) (declared : config.module.globals[initialized]? = some descriptor)
    (conditional : ScalarConditionalGlobal descriptor) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed = initialized ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  cases conditional with
  | integer condition yesScope noScope intTy yes no origin type initializer =>
    apply initGlobals_scalarConditional_core fuel initialized config before ambient types live descriptor condition yesScope noScope
      (.lit intTy yes) (.lit intTy no) (.int intTy yes) (.int intTy no) origin (.integer intTy yes) (.integer intTy no)
      world clear declared initializer
    · simp [type, Ty.nonfixed]
    · simpa [type] using ValueRepresentation.integer intTy yes
    · simpa [type] using ValueRepresentation.integer intTy no
    · simpa [type] using PointerTypedValue.integer intTy yes
    · simpa [type] using PointerTypedValue.integer intTy no
  | boolean condition yesScope noScope yes no origin type initializer =>
    apply initGlobals_scalarConditional_core fuel initialized config before ambient types live descriptor condition yesScope noScope
      (.bool yes) (.bool no) (.bool yes) (.bool no) origin (.boolean yes) (.boolean no)
      world clear declared initializer
    · simp [type, Ty.nonfixed]
    · simpa [type] using ValueRepresentation.boolean yes
    · simpa [type] using ValueRepresentation.boolean no
    · simpa [type] using PointerTypedValue.boolean yes
    · simpa [type] using PointerTypedValue.boolean no

#print axioms initGlobals_scalarConditional_single
end Goose.Proofs.ConstructionAcceptedExecution
