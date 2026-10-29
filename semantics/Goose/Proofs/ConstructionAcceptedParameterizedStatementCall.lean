import Goose.Proofs.ConstructionAcceptedParameterizedStatementStop
import Goose.Proofs.ConstructionAcceptedParameterizedTailCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execActivationBody_boundStatementsCall_earlier (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope : Nat) (pre : List (Nat × Value)) (statements : List Stmt)
    (target origin : Nat) (arguments : List Arg) (before boundState middle : ExecutionState)
    (ambient : OwnershipAmbient) (types middleTypes : RootTypes) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (ty : Ty) (frontier : Nat)
    (channels : activation.channels = [.register ty]) (frontierBound : frontier ≤ activation.act)
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 1) config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      boundState = .ok (.normal .unit) middle)
    (extended : RootTypesExtend types middleTypes) (acts : before.nextAct ≤ middle.nextAct) (scopes : before.nextScope ≤ middle.nextScope)
    (observed : EarlierCallerObservations frontier before middle types middleTypes)
    (inner : ∃ finalTypes finalLive finalAmbient,
      let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      let outcome := invokeCall fuel config environment target arguments [.register ty] origin middle
      RootTypesExtend middleTypes finalTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier middle (Goose.Proofs.Exit.stepState outcome) middleTypes finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ finalTypes finalLive finalAmbient,
      let outcome := execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some (.call target arguments origin)⟩ before
      RootTypesExtend types finalTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier before (Goose.Proofs.Exit.stepState outcome) types finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
  have body := execActivationBody_register_call_tail_withBindings fuel config activation scope pre statements before boundState middle ty target origin
    arguments channels bound normal
  obtain ⟨finalTypes, finalLive, finalAmbient, extension, nextActs, nextScopes, world, clear, nextObserved, result⟩ := inner
  cases execution : invokeCall fuel config environment target arguments [.register ty] origin middle with
  | stop reason after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at nextActs nextScopes world clear nextObserved result
    rw [body, execution]
    exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extension root ty (extended root ty found)),
      Nat.le_trans acts nextActs, Nat.le_trans scopes nextScopes, world, clear,
      observed.trans (Nat.le_refl _) nextObserved, trivial⟩
  | escape address carriers after | jump destination kind after =>
    simp only [environment] at execution
    simp [execution] at result
  | ok carriers after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at nextActs nextScopes world clear nextObserved result
    obtain ⟨rfl, value, rfl, represented⟩ := result
    rw [body, execution]
    have released := world.releaseScope config initialized after finalAmbient finalTypes finalLive regions pending activation scope before.nextScope
    exact ⟨finalTypes, _, finalAmbient, (fun root ty found => extension root ty (extended root ty found)),
      Nat.le_trans acts nextActs, Nat.le_trans scopes nextScopes, released, clear.releaseScope activation scope before.nextScope,
      (observed.trans (Nat.le_refl _) nextObserved).trans (Nat.le_refl _)
        (EarlierCallerObservations.releaseScope frontier activation scope before.nextScope after finalTypes frontierBound),
      rfl, value, rfl, represented⟩

#print axioms execActivationBody_boundStatementsCall_earlier
end Goose.Proofs.ConstructionAcceptedExecution
