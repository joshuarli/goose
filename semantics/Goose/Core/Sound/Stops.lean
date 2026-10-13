import Goose.Core.Sound.Basic

/-!
A function the validator finds never to return does not return: a call to it
never yields a result, at any fuel. This is a fact about the evaluator and the
analysis alone, with no appeal to typing.
-/

namespace Goose.Core.Sound
open Goose.Core

/-- The computation never yields a result. -/
def Never (x : M α) : Prop := ∀ s a s', x s ≠ .ok a s'

/-- Every result the computation yields satisfies `Q`. -/
def Only (Q : α → Prop) (x : M α) : Prop := ∀ s a s', x s = .ok a s' → Q a

theorem Never.bind_left {x : M α} {f : α → M β} (h : Never x) : Never (x >>= f) := by
  intro s b s' hb
  have hb' : M.bind' x f s = .ok b s' := hb
  unfold M.bind' at hb'
  cases hx : x s with
  | ok a s1 => exact h s a s1 hx
  | stop e s1 => rw [hx] at hb'; cases hb'

theorem Never.bind_only {Q : α → Prop} {x : M α} {f : α → M β} (hx : Only Q x)
    (hf : ∀ a, Q a → Never (f a)) : Never (x >>= f) := by
  intro s b s' hb
  have hb' : M.bind' x f s = .ok b s' := hb
  unfold M.bind' at hb'
  cases hxs : x s with
  | ok a s1 => rw [hxs] at hb'; exact hf a (hx s a s1 hxs) s1 b s' hb'
  | stop e s1 => rw [hxs] at hb'; cases hb'

theorem Never.bind_right {x : M α} {f : α → M β} (hf : ∀ a, Never (f a)) : Never (x >>= f) :=
  Never.bind_only (Q := fun _ => True) (fun _ _ _ _ => trivial) (fun a _ => hf a)

theorem never_stop (e : Stop) : Never (M.stop e : M α) := by
  intro s a s' h; cases h

theorem never_timeout : Never (timeout : M α) := never_stop _

theorem never_abort (k : AbortKind) (o : OriginId) : Never (abortAt k o : M α) := never_stop _

theorem never_fault (k : FaultKind) : Never (fault k : M α) := never_stop _

theorem Only.bind {Q : β → Prop} {x : M α} {f : α → M β} (hf : ∀ a, Only Q (f a)) :
    Only Q (x >>= f) := by
  intro s b s' hb
  have hb' : M.bind' x f s = .ok b s' := hb
  unfold M.bind' at hb'
  cases hxs : x s with
  | ok a s1 => rw [hxs] at hb'; exact hf a s1 b s' hb'
  | stop e s1 => rw [hxs] at hb'; cases hb'

theorem Only.pure {Q : α → Prop} {a : α} (h : Q a) : Only Q (pure a : M α) := by
  intro s b s' hb
  cases hb; exact h

theorem Only.of_never {Q : α → Prop} {x : M α} (h : Never x) : Only Q x :=
  fun s a s' hx => absurd hx (h s a s')

theorem pure_bind_M {α β : Type} (a : α) (f : α → M β) : (pure a >>= f) = f a := rfl

def IsNormal : Flow → Prop
  | .normal _ => True
  | _ => False

/-- A plain statement completes normally or not at all. -/
theorem plain_only (n : Nat) (cfg : Cfg) (env : Env) (st : Stmt) (h : st.isPlain = true) :
    Only IsNormal (execStmt n cfg env st) := by
  cases n with
  | zero => simp only [execStmt]; exact Only.of_never never_timeout
  | succ n =>
    cases st <;> simp only [Stmt.isPlain, reduceCtorEq] at h <;> simp only [execStmt] <;>
      repeat' (first
        | exact Only.pure trivial
        | exact Only.of_never (never_abort _ _)
        | exact Only.of_never (never_stop _)
        | refine Only.bind (fun _ => ?_)
        | split)

section Stops
variable (cfg : Cfg) (nr : ContextId → Bool)
  (hnr : ∀ c, nr c = true → ∀ n d vals, Never (enterCall n cfg d c vals))

include hnr in
/-- A statement that is a call to a function that never returns yields nothing. -/
theorem never_call_expr (n : Nat) (env : Env) (e : Expr) (o : OriginId)
    (h : (match e with | .call c _ _ => nr c | _ => false) = true) :
    Never (evalExpr n cfg env e) := by
  cases e <;> simp only [reduceCtorEq] at h
  rename_i c args org
  cases n with
  | zero => simp only [evalExpr]; exact never_timeout
  | succ n =>
    simp only [evalExpr]
    exact Never.bind_right (fun vals => hnr c h n _ vals)

structure StopsAt (n : Nat) : Prop where
  stmts : ∀ env ss, stmtsStop nr ss = true → Never (execStmts n cfg env ss)
  stmt : ∀ env st, Stmt.stops nr st = true → Never (execStmt n cfg env st)
  block : ∀ env pre b, Block.stops nr b = true → Never (execBlock n cfg env pre b)

include hnr in
theorem stopsAt : ∀ n, StopsAt cfg nr n
  | 0 => by
    refine ⟨?_, ?_, ?_⟩
    · intros; simp only [execStmts]; exact never_timeout
    · intros; simp only [execStmt]; exact never_timeout
    · intros; simp only [execBlock]; exact never_timeout
  | n + 1 => by
    have ih := stopsAt n
    refine ⟨?_, ?_, ?_⟩
    · intro env ss h
      cases ss with
      | nil => simp [stmtsStop] at h
      | cons st rest =>
        simp only [stmtsStop, Bool.or_eq_true, Bool.and_eq_true] at h
        simp only [execStmts]
        rcases h with h | ⟨hp, hr⟩
        · exact Never.bind_left (ih.stmt env st h)
        · refine Never.bind_only (plain_only n cfg env st hp) ?_
          intro fl hfl
          cases fl <;> simp only [IsNormal] at hfl
          exact ih.stmts env rest hr
    · intro env st h
      cases st with
      | abort msg o => simp only [execStmt]; exact never_abort _ _
      | exit e o =>
        simp only [execStmt]
        exact Never.bind_right (fun _ => Never.bind_right (fun _ => never_stop _))
      | expr e o =>
        simp only [execStmt]
        refine Never.bind_left (never_call_expr cfg nr hnr n env e o ?_)
        cases e <;> simp only [Stmt.stops, reduceCtorEq] at h ⊢
        exact h
      | ifS c t f o =>
        cases f with
        | none => simp [Stmt.stops] at h
        | some fb =>
          simp only [Stmt.stops, Bool.and_eq_true] at h
          simp only [execStmt]
          refine Never.bind_right (fun _ => Never.bind_right (fun branch => ?_))
          cases branch
          · simp only [Bool.false_eq_true, if_false]
            exact Never.bind_left (ih.block env [] fb h.2)
          · simp only [if_true]
            exact Never.bind_left (ih.block env [] t h.1)
      | _ => simp [Stmt.stops] at h
    · intro env pre b h
      obtain ⟨sc, ss, value⟩ := b
      simp only [Block.stops] at h
      simp only [execBlock]
      exact Never.bind_right (fun _ => Never.bind_right (fun _ => Never.bind_left (ih.stmts _ ss h)))

end Stops

/-- A context found never to return yields no result when entered. -/
theorem neverReturns_sound (m : Module) (prof : NumProfile) :
    ∀ (k : Nat) (c : ContextId), neverReturns m k c = true →
      ∀ n d vals, Never (enterCall n ⟨prof, m⟩ d c vals)
  | 0, c, h => by simp [neverReturns] at h
  | k + 1, c, h => by
    intro n d vals
    have ih := neverReturns_sound m prof k
    simp only [neverReturns] at h
    cases hc : m.contexts[c]? with
    | none => simp [hc] at h
    | some ctx =>
      cases hi : m.impls[ctx.impl]? with
      | none => simp [hc, hi] at h
      | some impl =>
        simp only [hc, hi] at h
        cases n with
        | zero => simp only [enterCall]; exact never_timeout
        | succ n =>
          simp only [enterCall]
          have body : Never (do
              let ctx ← lookupContext ⟨prof, m⟩ c
              let impl ← lookupImpl ⟨prof, m⟩ ctx.impl
              if impl.params.size = vals.length then do
                let act ← freshAct
                let fl ← execBlock n ⟨prof, m⟩ ⟨impl.vars, act, [], d + 1⟩
                  ((impl.params.toList.zip vals).map fun x => (x.fst.var, x.snd)) impl.body
                expectReturned fl
              else fault .arity) := by
            simp only [lookupContext, lookupImpl, hc, hi, pure_bind_M]
            split
            · exact Never.bind_right (fun _ => Never.bind_left
                ((stopsAt ⟨prof, m⟩ (neverReturns m k) ih n).block _ _ _ h))
            · exact never_fault _
          split
          · exact Never.bind_left never_timeout
          · exact body

theorem noReturn_sound (m : Module) (prof : NumProfile) (c : ContextId) (h : m.noReturn c = true) :
    ∀ n d vals, Never (enterCall n ⟨prof, m⟩ d c vals) :=
  neverReturns_sound m prof _ c h

end Goose.Core.Sound
