import Goose.Lower.Return
import Goose.Lower.UnwindChecks

namespace Goose.Lower.ReturnChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks

def returningStmt : Stmt := .ret (some (.read (.var 0))) 0

def returningBuilder (m : Core.Module) : LS :=
  (lowerStmt none returningStmt (lowerEnv m variables) scopedBuilder).2

def returningFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (returningBuilder m).blocks }

theorem concrete_return_site (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, returningFunction cfg.mod⟩ (0, 0) beforeFrame
      (execStmt fuel cfg beforeEnv returningStmt >>= prepareReturn beforeEnv)
      (fun flow pt' fr' => ∃ value, flow = .ret value ∧
        ReturnSite ⟨⟨cfg.profile, lower cfg.mod⟩, returningFunction cfg.mod⟩ pt' fr' value 0) := by
  apply stmt_ret_prepared_sim fuel none (some (.read (.var 0))) 0 rfl
    (lowerEnv cfg.mod variables) scopedBuilder (returningBuilder cfg.mod) () (0, 0)
    cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, returningFunction cfg.mod⟩ beforeFrame
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (returningBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def sourceModule : Core.Module :=
  let returning : Impl :=
    { name := "returning", params := #[], results := #[.int .i64], vars := variables,
      body := .mk 0 [.while (.bool true)
        (.mk 1 [.letS 0 (.lit .i64 9) 0, returningStmt] none) 0] none,
      summary := .unknown }
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [.expr (.call 0 [] 0) 0] none, summary := .unknown }
  { files := #["return.goose"], types := #[.int .i64], globals := #[],
    impls := #[returning, main], contexts := #[⟨0, "returning", [], [[]], []⟩,
      ⟨1, "main", [], [], []⟩], entry := 1, origins := #[⟨0, 1, "return"⟩] }

#guard match Core.validate sourceModule, GIR.validate (lower sourceModule) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match (execStmt 10 ⟨.release, sourceModule⟩ beforeEnv returningStmt >>= prepareReturn beforeEnv)
    localState with
  | .ok (.ret (Val.int IntTy.i64 9)) state => (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false
#guard match runAt ⟨⟨.release, lower sourceModule⟩, returningFunction sourceModule⟩ (0, 0)
    beforeFrame 20 localState with
  | .ok (Val.int IntTy.i64 9) state => (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false

#guard !Goose.Proofs.Lower.moduleOk sourceModule
#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 50 profile sourceModule, GIR.run 100 profile (lower sourceModule) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

end Goose.Lower.ReturnChecks
