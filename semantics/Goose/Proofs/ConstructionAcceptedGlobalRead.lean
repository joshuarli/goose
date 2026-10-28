import Goose.Proofs.ConstructionAcceptedMixedGlobalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_scalarGlobalRead_single (fuel initialized : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor sourceDescriptor : Global) (sourceId : Nat)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor)
    (sourceDeclared : config.module.globals[sourceId]? = some sourceDescriptor) (earlier : sourceId < initialized)
    (initializer : descriptor.init = .read (.global sourceId)) (sameType : descriptor.ty = sourceDescriptor.ty)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ completed nextLive,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive [] [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed = initialized ∧ FutureGlobalsClear config initialized after
      | .escape .. | .jump .. => False) := by
  obtain ⟨foundDescriptor, value, sourceFound, found, represented⟩ := world.globals.2 sourceId earlier
  have same : foundDescriptor = sourceDescriptor := Option.some.inj (sourceFound.symm.trans sourceDeclared)
  subst foundDescriptor
  have rootType := world.globalTypes sourceId sourceDescriptor sourceDeclared
  have pointers := (world.heap (.global sourceId) sourceDescriptor.ty value rootType found).2
  have valueScalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
    rcases scalar with ⟨intTy, same⟩ | same
    · rw [← sameType, same] at represented
      cases value <;> cases represented <;> simp_all [Ty.nonfixed]
    · rw [← sameType, same] at represented
      cases value <;> cases represented <;> simp_all [Ty.nonfixed]
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  let activated := { before with nextAct := before.nextAct + 1 }
  have activeWorld := (freshAct_acceptedWorld config initialized before ambient types live world).2
  have activeClear := clear.freshAct
  have foundActive : activated.objects.lookup (.global sourceId) = some value := found
  cases fuel with
  | zero =>
    have stopped : initGlobals 0 config [initialized] before = .stop .timeout activated := by
      simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, initializer, evalValue, timeout, EvalM.stop, activated]
    simp only [stopped, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, live, by omega, by omega, activeWorld, rfl, activeClear⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      have stopped : initGlobals 1 config [initialized] before = .stop .timeout activated := by
        simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, initializer, evalValue, evalPlace, timeout, EvalM.stop, activated]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, live, by omega, by omega, activeWorld, rfl, activeClear⟩
    | succ fuel =>
      have represented' : ValueRepresentation descriptor.ty value := by simpa [sameType] using represented
      have pointers' : PointerTypedValue types descriptor.ty value := by simpa [sameType] using pointers
      obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalarGlobal_world config initialized activated ambient types live descriptor value
        activeWorld declared valueScalar represented' pointers'
      have done : initGlobals (fuel + 2) config [initialized] before = .ok () after := by
        simp [initGlobals, declared, fixed, freshAct, EvalM.get, EvalM.set, bind, pure, initializer, evalValue, evalPlace,
          readLoc, found, readValuePath, bound, activated]
      simp only [done, Goose.Proofs.Exit.stepState]
      exact ⟨initialized + 1, (fun root => root = .global initialized ∨ live root), by omega, by omega,
        afterWorld, rfl, activeClear.bindGlobal value bound⟩

#print axioms initGlobals_scalarGlobalRead_single
end Goose.Proofs.ConstructionAcceptedExecution
