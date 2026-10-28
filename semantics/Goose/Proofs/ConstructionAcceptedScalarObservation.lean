import Goose.Proofs.ConstructionAcceptedScalarLocal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_scalarLocal_outside (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (descriptor : LocalVar) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (root other : Goose.Core.RootInst)
    (declared : environment.vars[id]? = some descriptor) (fixed : descriptor.ty.nonfixed = false)
    (resolved : rootOf environment id before = .ok root before)
    (unchanged : Goose.Proofs.Exit.stepState (evalValue fuel config environment expression before) = before)
    (executed : execStmt (fuel + 1) config environment (.letS id expression origin) before = .ok (.normal .unit) after)
    (different : other ≠ root) :
    after.objects.lookup other = before.objects.lookup other ∧
    after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
  rw [execStmt_scalarLocal_afterRoot fuel config environment id descriptor expression origin before root declared fixed resolved] at executed
  cases evaluated : evalValue fuel config environment expression before with
  | stop reason state | escape reason carriers state | jump target kind state =>
    simp [bind, evaluated] at executed
  | ok value state =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at unchanged
    subst state
    simp only [bind, evaluated] at executed
    cases bound : bindRoot root value before with
    | stop reason state | escape reason carriers state | jump target kind state => simp [bound] at executed
    | ok result state =>
      cases result
      simp only [bound, pure, ExecutionStep.ok.injEq, true_and] at executed
      subst after
      exact ⟨bindRoot_lookup_other root other value before state bound different,
        bindRoot_ordinals_other root other value before state bound different⟩

#print axioms execStmt_scalarLocal_outside
end Goose.Proofs.ConstructionAcceptedExecution
