import Goose.Proofs.ConstructionAcceptedScalarGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def MixedGlobalLiteral (descriptor : Global) : Prop :=
  ScalarGlobalLiteral descriptor ∨
    ∃ bytes bytesOrigin, descriptor.ty = .varr (.int .u8) ∧
      descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin

theorem initGlobals_mixed_single (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (literal : MixedGlobalLiteral descriptor) :
    ∃ completed nextLive regions,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive regions [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ regions = [] ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed < initialized + 1
      | .escape .. | .jump .. => False) := by
  rcases literal with scalar | ⟨bytes, bytesOrigin, ty, initializer⟩
  · obtain ⟨nextLive, nextWorld, next⟩ := initGlobals_scalar_single fuel initialized config before ambient types live descriptor
      world clear declared scalar
    cases execution : initGlobals fuel config [initialized] before with
    | ok value after =>
      cases value
      simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld next
      have positive := next.1
      simp only [ite_eq_right positive] at nextWorld
      exact ⟨initialized + 1, nextLive, [], by omega, by omega, nextWorld, rfl, rfl, next.2⟩
    | stop reason after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld next
      have zero := next.1
      subst fuel
      simp only [↓reduceIte] at nextWorld
      exact ⟨initialized, nextLive, [], by omega, by omega, nextWorld, by omega⟩
    | escape address carriers after | jump target kind after => simp only [execution] at next
  · have bound : initialized + 1 ≤ config.module.globals.size := by
      have inside := (Array.getElem?_eq_some_iff.mp declared).1
      omega
    have declarations : ∀ id, initialized ≤ id → id < initialized + 1 →
        ∃ other contents origin, config.module.globals[id]? = some other ∧
          other.ty = .varr (.int .u8) ∧ other.init = .bytes (.varr (.int .u8)) contents origin := by
      intro id lower upper
      have same : id = initialized := by omega
      subst id
      exact ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩
    obtain ⟨completed, nextLive, regions, lower, upper, nextWorld, nextFlow⟩ :=
      initGlobals_byteOwners_complete fuel initialized 1 config before ambient types live bound declarations world clear
    simp only [List.range'_one] at nextWorld nextFlow
    refine ⟨completed, nextLive, regions, lower, upper, nextWorld, ?_⟩
    cases execution : initGlobals fuel config [initialized] before with
    | ok value after =>
      cases value
      simp only [execution, Goose.Proofs.Exit.stepState] at nextFlow ⊢
      exact nextFlow
    | stop reason after => simp only [execution] at nextFlow ⊢; exact nextFlow
    | escape address carriers after | jump target kind after => simp only [execution] at nextFlow

theorem initGlobals_mixed_complete (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor, config.module.globals[id]? = some descriptor ∧ MixedGlobalLiteral descriptor) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      ∃ completed nextLive regions,
        let outcome := initGlobals fuel config (List.range' initialized count) before
        let after := Goose.Proofs.Exit.stepState outcome
        initialized ≤ completed ∧ completed ≤ initialized + count ∧
        AcceptedWorld config completed after ambient types nextLive regions [] ∧
        (match outcome with
        | .ok _ _ => completed = initialized + count ∧ regions = [] ∧ FutureGlobalsClear config completed after
        | .stop _ _ => completed < initialized + count
        | .escape .. | .jump .. => False) := by
  induction count with
  | zero =>
    intro fuel initialized config before ambient types live bound declarations world clear
    simp only [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, live, [], by omega, by omega, world, by simp, rfl, clear⟩
  | succ count ih =>
    intro fuel initialized config before ambient types live bound declarations world clear
    obtain ⟨descriptor, declared, literal⟩ := declarations initialized (Nat.le_refl _) (by omega)
    obtain ⟨completed, nextLive, regions, lower, upper, headWorld, headFlow⟩ :=
      initGlobals_mixed_single fuel initialized config before ambient types live descriptor world clear declared literal
    have factor := initGlobals_head_factor fuel config initialized (List.range' (initialized + 1) count)
    cases head : initGlobals fuel config [initialized] before with
    | stop reason after =>
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before = .stop reason after := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      exact ⟨completed, nextLive, regions, lower, by omega, headWorld, by omega⟩
    | escape address carriers after | jump target kind after => simp only [head] at headFlow
    | ok value middle =>
      cases value
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      obtain ⟨completedEq, regionsEq, nextClear⟩ := headFlow
      subst completed regions
      have tailDeclarations : ∀ id, initialized + 1 ≤ id → id < initialized + 1 + count →
          ∃ descriptor, config.module.globals[id]? = some descriptor ∧ MixedGlobalLiteral descriptor := by
        intro id lower upper
        exact declarations id (by omega) (by omega)
      obtain ⟨finalCompleted, finalLive, finalRegions, finalLower, finalUpper, finalWorld, finalFlow⟩ :=
        ih fuel (initialized + 1) config middle ambient types nextLive (by omega) tailDeclarations headWorld nextClear
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before =
          initGlobals fuel config (List.range' (initialized + 1) count) middle := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      refine ⟨finalCompleted, finalLive, finalRegions, by omega, by omega, finalWorld, ?_⟩
      cases tail : initGlobals fuel config (List.range' (initialized + 1) count) middle with
      | ok value after =>
        cases value
        simp only [tail] at finalFlow ⊢
        obtain ⟨completedEq, regionsEq, finalClear⟩ := finalFlow
        exact ⟨by omega, regionsEq, by simpa only [completedEq, tail, Goose.Proofs.Exit.stepState] using finalClear⟩
      | stop reason after => simp only [tail] at finalFlow ⊢; omega
      | escape address carriers after | jump target kind after => simp only [tail] at finalFlow

#print axioms initGlobals_mixed_single
#print axioms initGlobals_mixed_complete
end Goose.Proofs.ConstructionAcceptedExecution
