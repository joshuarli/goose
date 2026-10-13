import Goose.Core.Eval

/-!
Fuel monotonicity of `eval`: a result other than running out of fuel is the
result at every larger fuel.
-/

namespace Goose.Proofs.Fuel
open Goose.Core

def isTimeout : Stop → Bool
  | .timeout => true
  | _ => false

/-- `r'` extends `r`: every result but a timeout is kept. -/
def Agrees (r r' : Res α) : Prop :=
  (∀ a s, r = .ok a s → r' = .ok a s) ∧
  (∀ e s, r = .stop e s → isTimeout e = true ∨ r' = .stop e s)

/-- Computation `m'` extends `m`. -/
def MonoM (m m' : M α) : Prop := ∀ s, Agrees (m s) (m' s)

theorem MonoM.refl (m : M α) : MonoM m m := by
  intro s
  exact ⟨fun _ _ h => h, fun _ _ h => Or.inr h⟩

theorem MonoM.timeout (m : M α) : MonoM timeout m := by
  intro s
  refine ⟨fun a s' h => ?_, fun e s' h => ?_⟩
  · simp [Goose.Core.timeout, M.stop] at h
  · left
    simp [Goose.Core.timeout, M.stop] at h
    rw [← h.1]; rfl

theorem MonoM.bind {m m' : M α} {f f' : α → M β} (hm : MonoM m m')
    (hf : ∀ a, MonoM (f a) (f' a)) : MonoM (m >>= f) (m' >>= f') := by
  intro s
  show Agrees (M.bind' m f s) (M.bind' m' f' s)
  unfold M.bind'
  cases hr : m s with
  | ok a s1 =>
    have := (hm s).1 a s1 hr
    rw [this]
    simpa using hf a s1
  | stop e s1 =>
    rcases (hm s).2 e s1 hr with h | h
    · refine ⟨fun _ _ h' => (by cases h'), fun e' s' h' => ?_⟩
      left; cases h'; exact h
    · rw [h]
      exact ⟨fun _ _ h' => (by cases h'), fun e' s' h' => Or.inr h'⟩

end Goose.Proofs.Fuel

namespace Goose.Proofs.Fuel
open Goose.Core

theorem MonoM.mapList {f f' : α → M β} (h : ∀ a, MonoM (f a) (f' a)) (l : List α) :
    MonoM (mapList f l) (mapList f' l) := by
  induction l with
  | nil => exact MonoM.refl _
  | cons a as ih =>
    simp only [Goose.Core.mapList]
    exact MonoM.bind (h a) fun b => MonoM.bind ih fun bs => MonoM.refl _

/-- Every evaluation function at fuel `n` is extended by the one at fuel `k`. -/
structure MonoAll (n k : Nat) : Prop where
  expr : ∀ cfg env e, MonoM (evalExpr n cfg env e) (evalExpr k cfg env e)
  blockValue : ∀ cfg env b, MonoM (blockValue n cfg env b) (blockValue k cfg env b)
  arg : ∀ cfg env a, MonoM (evalArg n cfg env a) (evalArg k cfg env a)
  bound : ∀ cfg env len d b, MonoM (evalBound n cfg env len d b) (evalBound k cfg env len d b)
  place : ∀ cfg env p, MonoM (evalPlace n cfg env p) (evalPlace k cfg env p)
  view : ∀ cfg env v, MonoM (evalView n cfg env v) (evalView k cfg env v)
  call : ∀ cfg d c vs, MonoM (enterCall n cfg d c vs) (enterCall k cfg d c vs)
  block : ∀ cfg env pre b, MonoM (execBlock n cfg env pre b) (execBlock k cfg env pre b)
  stmts : ∀ cfg env ss, MonoM (execStmts n cfg env ss) (execStmts k cfg env ss)
  stmt : ∀ cfg env s, MonoM (execStmt n cfg env s) (execStmt k cfg env s)
  printArg : ∀ cfg env a, MonoM (execPrintArg n cfg env a) (execPrintArg k cfg env a)
  while_ : ∀ cfg env c b, MonoM (execWhile n cfg env c b) (execWhile k cfg env c b)
  range : ∀ cfg env x t i hi b, MonoM (execRange n cfg env x t i hi b) (execRange k cfg env x t i hi b)
  each : ∀ cfg env x idx r b vw i,
    MonoM (execEach n cfg env x idx r b vw i) (execEach k cfg env x idx r b vw i)

theorem MonoM.ite {c : Prop} [Decidable c] {t t' e e' : M α} (ht : MonoM t t') (he : MonoM e e') :
    MonoM (if c then t else e) (if c then t' else e') := by
  by_cases h : c <;> simp [h, ht, he]

macro "mono" : tactic => `(tactic| repeat' (first
  | with_reducible exact MonoM.refl _
  | (refine MonoM.ite ?_ ?_)
  | (cases ‹Flow›)
  | (cases ‹Option Expr›)
  | dsimp only
  | (refine MonoM.bind ?_ (fun _ => ?_))
  | (refine MonoM.mapList (fun _ => ?_) _)
  | with_reducible apply_assumption
  ))

set_option maxHeartbeats 400000 in
theorem step (n k : Nat) (ih : MonoAll n k) : MonoAll (n + 1) (k + 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := ih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cfg env e
    cases e with
    | structLit t es => cases t <;> simp only [evalExpr] <;> mono
    | _ => (try simp only [evalExpr]) <;> mono
  · intro cfg env b
    simp only [blockValue]; mono
  · intro cfg env a
    cases a <;> simp only [evalArg] <;> mono
  · intro cfg env len d b
    cases b <;> simp only [evalBound] <;> mono
  · intro cfg env p
    cases p <;> simp only [evalPlace] <;> mono
  · intro cfg env v
    cases v <;> simp only [evalView] <;> mono
  · intro cfg d c vs
    unfold enterCall; mono
  · intro cfg env pre b
    cases b; simp only [execBlock]; mono
  · intro cfg env ss
    cases ss <;> simp only [execStmts] <;> mono
  · intro cfg env s
    cases s with
    | ifS c t f o => cases f <;> simp only [execStmt] <;> mono
    | forEach x idx v r b o => cases idx <;> simp only [execStmt] <;> mono
    | ret e o => cases e <;> simp only [execStmt] <;> mono
    | _ => (try simp only [execStmt]) <;> mono
  · intro cfg env a
    cases a <;> simp only [execPrintArg] <;> mono
  · intro cfg env c b
    simp only [execWhile]; mono
  · intro cfg env x t i hi b
    (try simp only [execRange]); mono
  · intro cfg env x idx r b vw i
    unfold execEach; mono


theorem MonoAll.zero (k : Nat) : MonoAll 0 k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; simp only [evalExpr]; exact MonoM.timeout _
  · intros; unfold Goose.Core.blockValue; exact MonoM.timeout _
  · intros; simp only [evalArg]; exact MonoM.timeout _
  · intros; simp only [evalBound]; exact MonoM.timeout _
  · intros; simp only [evalPlace]; exact MonoM.timeout _
  · intros; simp only [evalView]; exact MonoM.timeout _
  · intros; simp only [enterCall]; exact MonoM.timeout _
  · intros; simp only [execBlock]; exact MonoM.timeout _
  · intros; simp only [execStmts]; exact MonoM.timeout _
  · intros; simp only [execStmt]; exact MonoM.timeout _
  · intros; simp only [execPrintArg]; exact MonoM.timeout _
  · intros; simp only [execWhile]; exact MonoM.timeout _
  · intros; simp only [execRange]; exact MonoM.timeout _
  · intros; unfold execEach; exact MonoM.timeout _

theorem monoAll : ∀ (n k : Nat), n ≤ k → MonoAll n k
  | 0, k, _ => MonoAll.zero k
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => step n k (monoAll n k (by omega))

theorem MonoM.initGlobals (n k : Nat) (h : n ≤ k) (cfg : Cfg) (gs : List GlobalId) :
    MonoM (initGlobals n cfg gs) (initGlobals k cfg gs) := by
  have H := monoAll n k h
  induction gs with
  | nil => exact MonoM.refl _
  | cons g rest ih =>
    simp only [Goose.Core.initGlobals]
    refine MonoM.bind (MonoM.refl _) (fun gl => MonoM.bind (MonoM.refl _) (fun act => ?_))
    exact MonoM.bind (H.expr _ _ _) (fun v => MonoM.bind (MonoM.refl _) (fun _ => ih))

theorem MonoM.runModule (n k : Nat) (h : n ≤ k) (cfg : Cfg) :
    MonoM (runModule n cfg) (runModule k cfg) := by
  have H := monoAll n k h
  simp only [Goose.Core.runModule]
  exact MonoM.bind (MonoM.initGlobals n k h cfg _) (fun _ =>
    MonoM.bind (H.call _ _ _ _) (fun _ => MonoM.refl _))

/-- `TH-FUEL-01`: a finished run is the result at every larger fuel. -/
theorem eval_fuel_mono (n k : Nat) (p : NumProfile) (m : Module) (o : Outcome) (t : String)
    (hk : n ≤ k) (h : eval n p m = .done o t) : eval k p m = .done o t := by
  have A := MonoM.runModule n k hk ⟨p, m⟩ St.initial
  unfold eval at h ⊢
  cases hr : runModule n ⟨p, m⟩ St.initial with
  | ok a s =>
    rw [hr] at h
    rw [A.1 a s hr]
    exact h
  | stop e s =>
    rw [hr] at h
    cases e with
    | abort kd org =>
      rw [(A.2 _ s hr).resolve_left (by simp [isTimeout])]
      exact h
    | exit code =>
      rw [(A.2 _ s hr).resolve_left (by simp [isTimeout])]
      exact h
    | fault kd => simp at h
    | timeout => simp at h

end Goose.Proofs.Fuel
