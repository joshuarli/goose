import Goose.Lower.ReflectionExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def NormalStmtReflection (fuel : Nat) (statement : Stmt) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (loop : Option LoopCtx)
    (ls after : LS) (fr : Frame) (pt : Pt) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerStmt loop statement le ls = ((),after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => execStmt n cfg env statement)
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state

def NormalStmtsReflection (fuel : Nat) (statements : List Stmt) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (loop : Option LoopCtx)
    (ls after : LS) (fr : Frame) (pt : Pt) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerStmts loop statements le ls = ((),after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => execStmts n cfg env statements)
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state

theorem normalStmtsReflection_nil (fuel : Nat) : NormalStmtsReflection fuel [] := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  simp only [lowerStmts,pure_run] at lowering
  obtain ⟨_,rfl⟩ := Prod.mk.inj lowering
  have reflection : ReflectAtFuel fuel cx pt fr (fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls fr' pt' []) state :=
    ReflectAtFuel.ret fuel ⟨rfl,Post.init rel point⟩
  exact reflection.of_source (fun _ => ⟨1,by simp only [execStmts]⟩)

theorem normalStmtsReflection_cons {fuel : Nat} {statement : Stmt} {rest : List Stmt}
    (head : NormalStmtReflection fuel statement)
    (tail : ∀ residual, residual ≤ fuel → NormalStmtsReflection residual rest) :
    NormalStmtsReflection fuel (statement :: rest) := by
  intro cfg env cx le loop ls after fr pt state rel point lowering extension
  obtain ⟨block,live,_,_⟩ := LS.pp_some point
  simp only [lowerStmts,bind_eq] at lowering
  obtain ⟨isLive,initial,test,lowering⟩ := lowering
  rw [isLive_run live] at test
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj test
  simp only [ite_true,bind_eq] at lowering
  obtain ⟨ignored,middle,headRun,tailRun⟩ := lowering
  cases ignored
  have middleExtension := extension.of_adv (advB_lowerStmts loop rest _ _ _ _ tailRun)
  have first := head cfg env cx le loop ls middle fr pt state rel point headRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => execStmt n cfg env statement >>= fun flow => match flow with
        | .normal _ => execStmts n cfg env rest
        | other => pure other)
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr after fr' pt' []) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).stmt cfg env statement) ?_
    · intro n flow next pt' fr' source matched residual bound
      obtain ⟨rfl,post⟩ := matched
      have second := tail residual bound cfg env cx le loop middle after fr' pt' next
        post.rel post.pp tailRun extension
      refine second.mono ?_
      intro flow' final pt'' fr'' matched'
      obtain ⟨flowEq,post'⟩ := matched'
      exact ⟨flowEq,by simpa only [List.nil_append] using post.comp post'⟩
    · intro flow n k bound
      cases flow with
      | normal value => exact (monoAll n k bound).stmts cfg env rest
      | _ => exact MonoM.refl _
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  simp only [execStmts,bind_apply]
  cases execStmt n cfg env statement state with
  | stop stop after => rfl
  | ok flow after => cases flow <;> rfl

theorem normalStmtsReflection_of_children {fuel : Nat} {statements : List Stmt}
    (children : ∀ statement ∈ statements, ∀ residual, residual ≤ fuel →
      NormalStmtReflection residual statement) : NormalStmtsReflection fuel statements := by
  induction statements generalizing fuel with
  | nil => exact normalStmtsReflection_nil fuel
  | cons statement rest induction =>
    apply normalStmtsReflection_cons (children statement (by simp) fuel (Nat.le_refl _))
    intro residual bound
    apply induction
    intro child member remaining remainingBound
    exact children child (by simp [member]) remaining (Nat.le_trans remainingBound bound)

end Goose.Lower
