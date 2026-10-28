import Goose.Lower.DemandReadAssignment
import Goose.Lower.DemandScalarAssignmentStatementAgreement

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem ExprSource.read_type {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) :
    ∃ info start finish, tyPlace source.typingEnv place start = .ok (info, finish) ∧ source.ty = info.ty := by
  have typed := source.typed
  simp only [tyExpr] at typed
  obtain ⟨info, finish, placed, typed⟩ := (st_bind_ok _ _ _ _).mp typed
  split at typed
  · exact ⟨info, source.typingStart, finish, placed, congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)⟩
  · exact ((rej_ok _ _ _ _).mp typed).elim

theorem ExprSource.global_read_target {cfg : Cfg} {env : Env} {state : St} {global : GlobalId}
    (source : ExprSource cfg env (.read (.global global)) state) {descriptor : Core.Global}
    (declared : cfg.mod.globals[global]? = some descriptor) (target : descriptor.ty.refTarget = true) :
    source.ty.refTarget = true := by
  obtain ⟨info, start, finish, placed, typeEq⟩ := source.read_type
  simp only [tyPlace, source.frame.mod_t, declared] at placed
  split at placed
  · have same := congrArg Prod.fst ((st_pure_ok _ _ _).mp placed)
    simp only at same
    rw [typeEq, same]
    exact target
  · exact ((rej_ok _ _ _ _).mp placed).elim

theorem ExprSource.local_read_target {cfg : Cfg} {env : Env} {state : St} {slot : VarId}
    (source : ExprSource cfg env (.read (.var slot)) state) {descriptor : LocalVar}
    (declared : env.vars[slot]? = some descriptor) (target : descriptor.ty.refTarget = true) :
    source.ty.refTarget = true := by
  obtain ⟨info, start, finish, placed, typeEq⟩ := source.read_type
  simp only [tyPlace] at placed
  obtain ⟨binding, _, looked, placed⟩ := (st_bind_ok _ _ _ _).mp placed
  simp only [varOf, source.frame.vars_t, declared] at looked
  split at looked
  · exact ((rej_ok _ _ _ _).mp looked).elim
  · have bindingEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp looked)
    simp only at bindingEq
    subst binding
    have infoEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp placed)
    simp only at infoEq
    rw [typeEq, infoEq]
    exact target

theorem ScalarAssignmentStatements.globalRead {cfg : Cfg} {env : Env} {place : Place}
    (destination : ScalarReadPlace place) (global : GlobalId) (origin : OriginId) {descriptor : Core.Global}
    (declared : cfg.mod.globals[global]? = some descriptor) (target : descriptor.ty.refTarget = true)
    {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
    ScalarAssignmentStatements cfg env (.assign place (.read (.global global)) origin :: rest) :=
  .readAssignment destination (.global global) origin (fun _ child _ => child.global_read_target declared target) tail

theorem ScalarAssignmentStatements.localRead {cfg : Cfg} {env : Env} {place : Place}
    (destination : ScalarReadPlace place) (slot : VarId) (origin : OriginId) {descriptor : LocalVar}
    (declared : env.vars[slot]? = some descriptor) (target : descriptor.ty.refTarget = true)
    {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
    ScalarAssignmentStatements cfg env (.assign place (.read (.var slot)) origin :: rest) :=
  .readAssignment destination (.slot slot) origin (fun _ child _ => child.local_read_target declared target) tail

#print axioms ExprSource.global_read_target
#print axioms ExprSource.local_read_target
#print axioms ScalarAssignmentStatements.globalRead
#print axioms ScalarAssignmentStatements.localRead

end Goose.Lower
