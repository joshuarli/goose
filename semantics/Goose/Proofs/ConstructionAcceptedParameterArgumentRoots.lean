import Goose.Proofs.ConstructionAcceptedParameterTargetMapping
namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpArgs_singleByValue_roots {env : PEnv} {expression : Expr} {before middle after : RState}
    {roots : List RootRef} {argumentRoots : List (List RootRef)}
    (operand : rpExpr env expression before = .ok (roots, middle))
    (checked : rpArgs env [.byVal expression] before = .ok (argumentRoots, after)) : argumentRoots = [roots] := by
  simp only [rpArgs, operand, bind, StateT.bind, Except.bind] at checked
  repeat' first
    | split at checked
    | simp_all
  rename_i captured capturedValue interior interiorValue retained retainedValue capturedEq interiorEq retainedEq
  change Except.ok (([], ({} : Eff)), _) = Except.ok capturedValue at capturedEq
  cases capturedEq
  simpa [pure, StateT.pure, Except.pure] using congrArg Prod.fst (Except.ok.inj checked) |>.symm

theorem scalarLocal_singleArgument_roots (source : PEnv) (id : Nat) (descriptor : LocalVar)
    (before after : RState) (roots : List (List RootRef))
    (declared : source.impl.vars[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (rooted : rpArgs source [.byVal (.read (.var id))] before = .ok (roots, after)) : roots = [[]] := by
  cases operand : rpExpr source (.read (.var id)) before with
  | error error => simp [rpArgs, bind, StateT.bind, Except.bind, operand] at rooted
  | ok pair =>
    obtain ⟨operandRoots, middle⟩ := pair
    have same := rpArgs_singleByValue_roots operand rooted
    have empty := scalarLocal_argument_roots source id descriptor before middle operandRoots declared scalar operand
    simpa [empty] using same

#print axioms rpArgs_singleByValue_roots
#print axioms scalarLocal_singleArgument_roots

end Goose.Proofs.ConstructionAcceptedExecution
