import Goose.Proofs.ConstructionAcceptedNestedComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private theorem nestedGlobal_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

private theorem nestedGlobal_forAll_member {α : Type} (rows : List α) (action : α → Goose.Core.V Unit)
    (checked : Goose.Core.forAll rows action = .ok ()) : ∀ row ∈ rows, action row = .ok () := by
  induction rows with
  | nil => intro row absent; cases absent
  | cons row rows ih =>
    simp only [Goose.Core.forAll, bind, Except.bind] at checked
    cases first : action row with
    | error failure => simp only [first] at checked; cases checked
    | ok value =>
      cases value
      simp only [first] at checked
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact first
      · exact ih checked selected member

elab "unfold_nested_capacity" : tactic => do
  let name (part : String) := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") part
  let capacity := Lean.mkIdent (name "noteReceivingCapacity")
  let receiving := Lean.mkIdent (name "receivingCapacity")
  let checked := Lean.mkIdent `checked
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $capacity:ident $receiving:ident at $checked:ident))

theorem initializerRootFacts_effects_scalar (config : EvalConfig) (id : Nat) (descriptor : Global)
    (names : Array (List RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (present : config.module.globals[id]? = some descriptor)
    (facts : InitializerRootFactsAt config.module id calls names)
    (roots : List RootRef) (after : RState)
    (rooted : rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ = .ok (roots, after))
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    GlobalEffectTargetsBounded after.eff id := by
  obtain ⟨effects, checked, callsEq⟩ := facts
  unfold_initializer_root_checker
  simp only [present] at checked
  rcases scalar with ⟨intTy, tyEq⟩ | tyEq
  all_goals
    rw [tyEq] at checked
    simp only [initializerSource] at rooted
    simp only [StateT.run, bind, StateT.bind, Except.bind, rooted] at checked
    unfold_nested_capacity
    simp only [pure, StateT.pure, Except.pure] at checked
    cases unknown : after.eff.unknown with
    | true => simp [unknown, Goose.Core.reject] at checked
    | false =>
      simp only [unknown, Bool.false_eq_true, ↓reduceIte] at checked
      let action : Target → Goose.Core.V Unit := fun target => match target with
        | .global global => if global < id then .ok () else Goose.Core.reject .call
            s!"initializer of global {descriptor.name} reaches global {global}, which is not initialized before it"
        | .param _ => .ok ()
      have targets : Goose.Core.forAll after.eff.accessTargets action = .ok () := by
        have original := checked
        change (Except.bind (Goose.Core.forAll after.eff.accessTargets _) _) = _ at original
        cases run : Goose.Core.forAll after.eff.accessTargets action with
        | ok result => cases result; rfl
        | error failure =>
          change (Except.bind (Goose.Core.forAll after.eff.accessTargets action) _) = _ at original
          rw [run] at original
          cases original
      intro global member
      have observed := nestedGlobal_forAll_member after.eff.accessTargets action targets (.global global) member
      by_cases inside : global < id
      · exact inside
      · simp [action, inside, Goose.Core.reject] at observed

theorem accepted_nestedGlobal_checked (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame config id before.nextAct names
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] ∧ AcceptedFrame config accepted frame activated types ∧
      CheckedValue frame descriptor.init descriptor.ty roots typingAfter rootsAfter := by
  obtain ⟨names, activeWorld, frameSource, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  have sameType : ty = descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at adapts ⊢ <;>
      cases ty <;> simp_all [Ty.adaptsTo, Ty.element?]
  subst ty
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  have origin := frameSource.compatible.origin
  change SourceOrigin accepted frame at origin
  change ∃ descriptor, config.module.globals[id]? = some descriptor ∧ _ at origin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, calls, facts, closure⟩ := origin
  have bounded := initializerRootFacts_effects_scalar config id descriptor names calls present facts roots rootsAfter rooted scalar
  have available : GlobalEffectsAvailable frame.interpretation id rootsAfter.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact bounded other member
    | param parameter => exact instantiated.1.elim
  exact ⟨names, roots, typingAfter, rootsAfter, activeWorld, frameSource, typed, rooted, available⟩

theorem initGlobals_nestedScalar_single (fuel id : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config id before ambient types live [] [])
    (clear : FutureGlobalsClear config id before) (present : config.module.globals[id]? = some descriptor)
    (form : NestedScalarExpression descriptor.init) (scalars : FlatGlobalsAreScalar config)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [id] before
      let after := Goose.Proofs.Exit.stepState outcome
      id ≤ completed ∧ completed ≤ id + 1 ∧ AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with | .ok _ _ => completed = id + 1 ∧ FutureGlobalsClear config completed after | .stop _ _ => completed = id ∧ FutureGlobalsClear config id after | .escape .. | .jump .. => False) := by
  obtain ⟨names, roots, typingAfter, rootsAfter, activeWorld, frameSource, checked⟩ :=
    accepted_nestedGlobal_checked config accepted id descriptor before ambient types live world clear present scalar
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  let activated := { before with nextAct := before.nextAct + 1 }
  let environment : RuntimeActivation := ⟨0, before.nextAct, #[], [], []⟩
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  have safe := nestedScalarExpression_complete form fuel config accepted frame activated ambient types live activeWorld frameSource
    rfl (by simp [frame, scalarGlobalInitializerFrame, EntryInterpretation])
    scalars descriptor.ty roots typingAfter rootsAfter checked
  change NestedValueOutcome config accepted frame ambient types live descriptor.ty
    (evalValue fuel config environment descriptor.init activated) at safe
  cases execution : evalValue fuel config environment descriptor.init activated with
  | stop reason after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    have stopped : initGlobals fuel config [id] before = .stop reason after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, environment, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨id, live, by omega, by omega, safe.1, rfl, safe.2.1.futureGlobals⟩
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, execution] at safe
    exact safe.2.2.elim
  | ok value evaluated =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at safe <;>
        cases value <;> cases safe.2.2.1 <;> simp_all [Ty.nonfixed]
    have evaluatedClear : FutureGlobalsClear config id evaluated := safe.2.1.futureGlobals
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config id evaluated ambient types live descriptor
      value safe.1 present scalarValue safe.2.2.1 safe.2.2.2
    have done : initGlobals fuel config [id] before = .ok () after := by
      simp [initGlobals, present, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, execution, bound, environment, activated]
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨id + 1, (fun root => root = .global id ∨ live root), by omega, by omega,
      afterWorld, rfl, evaluatedClear.bindGlobal value bound⟩

#print axioms initGlobals_nestedScalar_single
#print axioms accepted_nestedGlobal_checked
#print axioms initializerRootFacts_effects_scalar
end Goose.Proofs.ConstructionAcceptedExecution
