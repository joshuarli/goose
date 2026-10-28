import Goose.Proofs.ConstructionAcceptedMixedAssignModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem bindRoot_scalarGlobal_world (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (value : Value)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (declared : config.module.globals[initialized]? = some descriptor)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value) :
    ∃ after, bindRoot (.global initialized) value before = .ok () after ∧
      AcceptedWorld config (initialized + 1) after ambient types
        (fun root => root = .global initialized ∨ live root) [] [] := by
  have registered := world.globalTypes initialized descriptor declared
  obtain ⟨after, evaluated, post⟩ := bindRoot_scalar_registered_world config initialized before ambient types live
    (.global initialized) descriptor.ty value [] [] world scalar registered represented pointers
  obtain ⟨result, bound, objects⟩ := bindRoot_objects (.global initialized) value before
  have same := (ExecutionStep.ok.inj (bound.symm.trans evaluated)).2
  subst result
  have present : after.objects.lookup (.global initialized) = some value := by simp only [objects, List.lookup, beq_self_eq_true]
  refine ⟨after, evaluated, ⟨post.ownership, ?_, post.globalTypes, post.layouts, post.typeFrontier, post.syntheticFrontier,
    post.heap, post.objectsRegistered, post.ordinalsRegistered, post.backing, post.protections, post.carriers⟩, ?_⟩
  · refine ⟨(Array.getElem?_eq_some_iff.mp declared).1, ?_⟩
    intro id available
    have cases : id < initialized ∨ id = initialized := Nat.lt_succ_iff_lt_or_eq.mp available
    rcases cases with prior | same
    · exact post.globals.2 id prior
    · subst id
      exact ⟨descriptor, value, declared, present, (post.heap _ _ _ registered present).1⟩
  · intro id available
    have cases : id < initialized ∨ id = initialized := Nat.lt_succ_iff_lt_or_eq.mp available
    rcases cases with prior | same
    · exact post.globalLive id prior
    · subst id; exact Or.inl rfl

inductive ScalarGlobalLiteral (descriptor : Global) : Prop
  | integer (intTy : Goose.Core.IntTy) (number : Int)
      (type : descriptor.ty = .int intTy) (initializer : descriptor.init = .lit intTy number) : ScalarGlobalLiteral descriptor
  | boolean (boolean : Bool)
      (type : descriptor.ty = .bool) (initializer : descriptor.init = .bool boolean) : ScalarGlobalLiteral descriptor

private theorem initGlobals_scalar_literal_single (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (value : Value)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (evaluates : ∀ remaining environment, evalValue (remaining + 1) config environment descriptor.init = pure value)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value) :
    ∃ nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config (if fuel = 0 then initialized else initialized + 1) after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => fuel ≠ 0 ∧ FutureGlobalsClear config (initialized + 1) after
      | .stop _ _ => fuel = 0 ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  let activated := { before with nextAct := before.nextAct + 1 }
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  have activeClear := clear.freshAct
  cases fuel with
  | zero =>
    have stopped : initGlobals 0 config [initialized] before = .stop .timeout activated := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, evalValue, timeout, EvalM.stop, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState, ↓reduceIte]
    exact ⟨live, activeWorld, trivial, activeClear⟩
  | succ fuel =>
    obtain ⟨after, bound, nextWorld⟩ := bindRoot_scalarGlobal_world config initialized activated ambient types live descriptor value
      activeWorld declared scalar represented pointers
    have done : initGlobals (fuel + 1) config [initialized] before = .ok () after := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, evaluates, pure, bound, activated]
    simp only [done, Goose.Proofs.Exit.stepState, Nat.succ_ne_zero, ↓reduceIte]
    exact ⟨(fun root => root = .global initialized ∨ live root), nextWorld, Nat.succ_ne_zero _, activeClear.bindGlobal value bound⟩

theorem initGlobals_scalar_single (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (literal : ScalarGlobalLiteral descriptor) :
    ∃ nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config (if fuel = 0 then initialized else initialized + 1) after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => fuel ≠ 0 ∧ FutureGlobalsClear config (initialized + 1) after
      | .stop _ _ => fuel = 0 ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  cases literal with
  | integer intTy number type initializer =>
    apply initGlobals_scalar_literal_single fuel initialized config before ambient types live descriptor (.int intTy number)
      world clear declared
    · simp [type, Ty.nonfixed]
    · intro remaining environment; simp [initializer, evalValue]
    · exact Or.inl ⟨intTy, number, rfl⟩
    · simpa [type] using (ValueRepresentation.integer intTy number)
    · simpa [type] using (PointerTypedValue.integer intTy number)
  | boolean boolean type initializer =>
    apply initGlobals_scalar_literal_single fuel initialized config before ambient types live descriptor (.bool boolean)
      world clear declared
    · simp [type, Ty.nonfixed]
    · intro remaining environment; simp [initializer, evalValue]
    · exact Or.inr ⟨boolean, rfl⟩
    · simpa [type] using (ValueRepresentation.boolean boolean)
    · simpa [type] using (PointerTypedValue.boolean boolean)

#print axioms initGlobals_scalar_single
#print axioms bindRoot_scalarGlobal_world
end Goose.Proofs.ConstructionAcceptedExecution
