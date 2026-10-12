import Goose.Core.Eval
import Goose.Core.Validate
import Goose.Share.Quotient
import Goose.Share.EqualSound

namespace Goose.Proofs.Share

open Goose.Core Goose.Share

/-- The evaluator's monad satisfies the monad laws, which lets `simp` normalize
the `do` blocks of the evaluator. -/
instance instLawfulMonadM : LawfulMonad M := LawfulMonad.mk'
  M
  (id_map := fun x => by
    funext s
    show (match x s with | .ok a s' => Res.ok a s' | .stop e s' => .stop e s') = x s
    cases x s <;> rfl)
  (pure_bind := fun a f => rfl)
  (bind_assoc := fun x f g => by
    funext s
    show (match (match x s with | .ok a s' => f a s' | .stop e s' => .stop e s') with
      | .ok a s' => g a s' | .stop e s' => .stop e s') =
      (match x s with
        | .ok a s' => (match f a s' with | .ok b s'' => g b s'' | .stop e s'' => .stop e s'')
        | .stop e s' => .stop e s')
    cases x s <;> rfl)

/-- A stopped computation ignores what would follow. -/
theorem fault_bind {α β : Type} (k : FaultKind) (f : α → M β) : (fault k >>= f) = fault k := rfl

/-! ### Renaming by the identity -/

mutual
theorem renPlace_id : ∀ p : Place, renPlace id p = p
  | .var _ => rfl
  | .global _ => rfl
  | .deref e => by simp [renPlace, renExpr_id e]
  | .elem v i o => by simp [renPlace, renView_id v, renExpr_id i]

theorem renView_id : ∀ v : View, renView id v = v
  | .of p => by simp [renView, renPlace_id p]
  | .val e => by simp [renView, renExpr_id e]

theorem renBound_id : ∀ b : Bound, renBound id b = b
  | .expr e => by simp [renBound, renExpr_id e]
  | .fromEnd e => by simp [renBound, renExpr_id e]
  | .omitted => rfl

theorem renExpr_id : ∀ e : Expr, renExpr id e = e
  | .lit .. => rfl
  | .bool _ => rfl
  | .read p => by simp [renExpr, renPlace_id p]
  | .ref _ p => by simp [renExpr, renPlace_id p]
  | .slice _ v lo hi _ => by simp [renExpr, renView_id v, renBound_id lo, renBound_id hi]
  | .len v => by simp [renExpr, renView_id v]
  | .un _ e _ => by simp [renExpr, renExpr_id e]
  | .bin _ a b _ => by simp [renExpr, renExpr_id a, renExpr_id b]
  | .cmp _ a b => by simp [renExpr, renExpr_id a, renExpr_id b]
  | .and a b => by simp [renExpr, renExpr_id a, renExpr_id b]
  | .or a b => by simp [renExpr, renExpr_id a, renExpr_id b]
  | .not e => by simp [renExpr, renExpr_id e]
  | .conv _ _ e _ => by simp [renExpr, renExpr_id e]
  | .call c args _ => by simp [renExpr, renArgs_id args]
  | .push p e => by simp [renExpr, renPlace_id p, renExpr_id e]
  | .ifE c t f => by simp [renExpr, renExpr_id c, renBlock_id t, renBlock_id f]
  | .blockE b => by simp [renExpr, renBlock_id b]
  | .arrLit _ es => by simp [renExpr, renExprs_id es]
  | .fill _ e => by simp [renExpr, renExpr_id e]

theorem renExprs_id : ∀ es : List Expr, renExprs id es = es
  | [] => rfl
  | e :: es => by simp [renExprs, renExpr_id e, renExprs_id es]

theorem renArg_id : ∀ a : Arg, renArg id a = a
  | .byVal e => by simp [renArg, renExpr_id e]
  | .byRef _ p => by simp [renArg, renPlace_id p]

theorem renArgs_id : ∀ as : List Arg, renArgs id as = as
  | [] => rfl
  | a :: as => by simp [renArgs, renArg_id a, renArgs_id as]

theorem renOptExpr_id : ∀ e : Option Expr, renOptExpr id e = e
  | none => rfl
  | some e => by simp [renOptExpr, renExpr_id e]

theorem renBlock_id : ∀ b : Block, renBlock id b = b
  | .mk _ ss v => by simp [renBlock, renStmts_id ss, renOptExpr_id v]

theorem renOptBlock_id : ∀ b : Option Block, renOptBlock id b = b
  | none => rfl
  | some b => by simp [renOptBlock, renBlock_id b]

theorem renPrintArg_id : ∀ a : PrintArg, renPrintArg id a = a
  | .text _ => rfl
  | .expr e => by simp [renPrintArg, renExpr_id e]

theorem renPrintArgs_id : ∀ as : List PrintArg, renPrintArgs id as = as
  | [] => rfl
  | a :: as => by simp [renPrintArgs, renPrintArg_id a, renPrintArgs_id as]

theorem renStmt_id : ∀ s : Stmt, renStmt id s = s
  | .letS .. => by simp [renStmt, renExpr_id]
  | .assign p e _ => by simp [renStmt, renPlace_id p, renExpr_id e]
  | .assignOp _ p e _ => by simp [renStmt, renPlace_id p, renExpr_id e]
  | .rebind _ e _ => by simp [renStmt, renExpr_id e]
  | .expr e _ => by simp [renStmt, renExpr_id e]
  | .append p v _ => by simp [renStmt, renPlace_id p, renView_id v]
  | .ifS c t f _ => by simp [renStmt, renExpr_id c, renBlock_id t, renOptBlock_id f]
  | .while c b _ => by simp [renStmt, renExpr_id c, renBlock_id b]
  | .forRange _ lo hi b _ => by simp [renStmt, renExpr_id lo, renExpr_id hi, renBlock_id b]
  | .forEach _ _ v _ b _ => by simp [renStmt, renView_id v, renBlock_id b]
  | .ret e _ => by simp [renStmt, renOptExpr_id e]
  | .brk _ => rfl
  | .cont _ => rfl
  | .print as _ => by simp [renStmt, renPrintArgs_id as]
  | .assertS e _ => by simp [renStmt, renExpr_id e]
  | .abort .. => rfl
  | .exit e _ => by simp [renStmt, renExpr_id e]

theorem renStmts_id : ∀ ss : List Stmt, renStmts id ss = ss
  | [] => rfl
  | s :: ss => by simp [renStmts, renStmt_id s, renStmts_id ss]
end

theorem renArgs_eq_map (r : CtxMap) : ∀ l, renArgs r l = l.map (renArg r)
  | [] => rfl
  | a :: as => by simp [renArgs, renArgs_eq_map r as]

theorem renExprs_eq_map (r : CtxMap) : ∀ l, renExprs r l = l.map (renExpr r)
  | [] => rfl
  | a :: as => by simp [renExprs, renExprs_eq_map r as]

theorem renPrintArgs_eq_map (r : CtxMap) : ∀ l, renPrintArgs r l = l.map (renPrintArg r)
  | [] => rfl
  | a :: as => by simp [renPrintArgs, renPrintArgs_eq_map r as]

/-- Mapping a monadic function over a list commutes with renaming the
elements first, when the function agrees with its counterpart on renamed
elements. Stated for the evaluator's monad directly because the proof
unfolds `List.mapM`. -/
theorem mapM_sim {α β γ : Type} (f : α → M γ) (g : β → M γ) (h : α → β)
    (hf : ∀ a, f a = g (h a)) (l : List α) : l.mapM f = (l.map h).mapM g := by
  unfold List.mapM
  suffices ∀ acc, List.mapM.loop f l acc = List.mapM.loop g (l.map h) acc from this []
  induction l with
  | nil => intro acc; rfl
  | cons a as ih => intro acc; simp only [List.mapM.loop, List.map, hf a, ih]


section Simulation

variable {p : NumProfile} {m m' : Module} {ρ : ImplId → CtxMap}

/-- A call's two table lookups are one lookup of `resolve`. -/
theorem lookup_chain {α : Type} (cfg : Cfg) (c : ContextId) (k : Impl → M α) :
    (do let ctx ← lookupContext cfg c
        let impl ← lookupImpl cfg ctx.impl
        k impl) =
      (match resolve cfg.mod c with
        | some i => k i
        | none => fault .unbound) := by
  unfold lookupContext resolve
  cases h : cfg.mod.contexts[c]? with
  | none => simp [fault_bind]
  | some ctx =>
    simp only [Option.bind_some]
    unfold lookupImpl
    cases h2 : cfg.mod.impls[ctx.impl]? <;> simp [h2, fault_bind]

theorem resolve_eq_map_snd (m : Module) (c : ContextId) :
    resolve m c = (resolveIndexed m c).map Prod.snd := by
  unfold resolve resolveIndexed
  cases m.contexts[c]? with
  | none => rfl
  | some ctx => cases hh : m.impls[ctx.impl]? <;> simp [hh]

-- The statements below take the callee renaming `r` of the code being run as
-- an argument: a body is renamed by `ρ g`, a global's initializer is not
-- renamed, and each is compatible with the tables (`Resolves`).

mutual
theorem evalExpr_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (e : Expr),
    evalExpr n ⟨p, m⟩ env e = evalExpr n ⟨p, m'⟩ env (renExpr r e)
  | r, _, 0, env, e => by simp [evalExpr]
  | r, hr, n + 1, env, e => by
    cases e with
    | call c args o =>
      simp only [evalExpr, renExpr, renArgs_eq_map]
      rw [mapM_sim _ (evalArg n ⟨p, m'⟩ env) (renArg r)
        (fun a => evalArg_sim hρ r hr n env a)]
      have call : ∀ depth c vals, enterCall n ⟨p, m⟩ depth c vals =
          enterCall n ⟨p, m'⟩ depth (r c) vals :=
        fun depth c vals => enterCall_sim hρ n depth c (r c) vals (hr c)
      simp only [call]
    | arrLit t es =>
      simp only [evalExpr, renExpr, renExprs_eq_map]
      rw [mapM_sim _ (evalExpr n ⟨p, m'⟩ env) (renExpr r)
        (fun a => evalExpr_sim hρ r hr n env a)]
    | _ => simp [evalExpr, renExpr, evalExpr_sim hρ r hr n, evalPlace_sim hρ r hr n,
        evalView_sim hρ r hr n, evalBound_sim hρ r hr n, blockValue_sim hρ r hr n]

theorem blockValue_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (b : Block),
    blockValue n ⟨p, m⟩ env b = blockValue n ⟨p, m'⟩ env (renBlock r b)
  | r, _, 0, env, b => by simp [blockValue]
  | r, hr, n + 1, env, b => by simp [blockValue, execBlock_sim hρ r hr n]

theorem evalArg_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (a : Arg),
    evalArg n ⟨p, m⟩ env a = evalArg n ⟨p, m'⟩ env (renArg r a)
  | r, _, 0, env, a => by simp [evalArg]
  | r, hr, n + 1, env, a => by
    cases a <;> simp [evalArg, renArg, evalExpr_sim hρ r hr n, evalPlace_sim hρ r hr n]

theorem evalBound_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env)
      (len : Nat) (dflt : Int) (b : Bound),
    evalBound n ⟨p, m⟩ env len dflt b = evalBound n ⟨p, m'⟩ env len dflt (renBound r b)
  | r, _, 0, env, len, dflt, b => by simp [evalBound]
  | r, hr, n + 1, env, len, dflt, b => by
    cases b <;> simp [evalBound, renBound, evalExpr_sim hρ r hr n]

theorem evalPlace_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (pl : Place),
    evalPlace n ⟨p, m⟩ env pl = evalPlace n ⟨p, m'⟩ env (renPlace r pl)
  | r, _, 0, env, pl => by simp [evalPlace]
  | r, hr, n + 1, env, pl => by
    cases pl <;> simp [evalPlace, renPlace, evalExpr_sim hρ r hr n, evalView_sim hρ r hr n]

theorem evalView_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (v : View),
    evalView n ⟨p, m⟩ env v = evalView n ⟨p, m'⟩ env (renView r v)
  | r, _, 0, env, v => by simp [evalView]
  | r, hr, n + 1, env, v => by
    cases v <;> simp [evalView, renView, evalExpr_sim hρ r hr n, evalPlace_sim hρ r hr n]

theorem enterCall_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (n : Nat) (depth : Nat) (c c' : ContextId) (vals : List Val),
    Resolves m m' ρ c' c →
    enterCall n ⟨p, m⟩ depth c vals = enterCall n ⟨p, m'⟩ depth c' vals
  | 0, depth, c, c', vals, _ => by simp [enterCall]
  | n + 1, depth, c, c', vals, hc => by
    unfold Resolves at hc
    simp only [enterCall, lookup_chain, hc, resolve_eq_map_snd m c]
    cases hi : resolveIndexed m c with
    | none => rfl
    | some gi =>
      obtain ⟨g, i⟩ := gi
      simp [renImpl, execBlock_sim hρ (ρ g) (hρ g) n]

theorem execBlock_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env)
      (pre : List (VarId × Val)) (b : Block),
    execBlock n ⟨p, m⟩ env pre b = execBlock n ⟨p, m'⟩ env pre (renBlock r b)
  | r, _, 0, env, pre, b => by simp [execBlock]
  | r, hr, n + 1, env, pre, .mk sc stmts value => by
    cases value with
    | none => simp [execBlock, renBlock, renOptExpr, execStmts_sim hρ r hr n]
    | some e =>
      simp only [execBlock, renBlock, renOptExpr, execStmts_sim hρ r hr n]
      congr 1; funext si; congr 1; funext fl; congr 1; funext flow
      cases flow <;> simp [evalExpr_sim hρ r hr n]

theorem execStmts_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (ss : List Stmt),
    execStmts n ⟨p, m⟩ env ss = execStmts n ⟨p, m'⟩ env (renStmts r ss)
  | r, _, 0, env, ss => by simp [execStmts]
  | r, hr, n + 1, env, [] => by simp [execStmts, renStmts]
  | r, hr, n + 1, env, s :: rest => by
    simp [execStmts, renStmts, execStmt_sim hρ r hr n, execStmts_sim hρ r hr n]

theorem execStmt_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (s : Stmt),
    execStmt n ⟨p, m⟩ env s = execStmt n ⟨p, m'⟩ env (renStmt r s)
  | r, _, 0, env, s => by simp [execStmt]
  | r, hr, n + 1, env, s => by
    cases s with
    | print args o =>
      simp only [execStmt, renStmt, renPrintArgs_eq_map]
      rw [mapM_sim _ (execPrintArg n ⟨p, m'⟩ env) (renPrintArg r)
        (fun a => execPrintArg_sim hρ r hr n env a)]
    | ifS c t f o =>
      cases f <;> simp [execStmt, renStmt, renOptBlock, evalExpr_sim hρ r hr n,
        execBlock_sim hρ r hr n]
    | ret e o => cases e <;> simp [execStmt, renStmt, renOptExpr, evalExpr_sim hρ r hr n]
    | _ => simp [execStmt, renStmt, evalExpr_sim hρ r hr n, evalPlace_sim hρ r hr n,
        evalView_sim hρ r hr n, execWhile_sim hρ r hr n, execRange_sim hρ r hr n,
        execEach_sim hρ r hr n]

theorem execPrintArg_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env) (a : PrintArg),
    execPrintArg n ⟨p, m⟩ env a = execPrintArg n ⟨p, m'⟩ env (renPrintArg r a)
  | r, _, 0, env, a => by simp [execPrintArg]
  | r, hr, n + 1, env, a => by
    cases a <;> simp [execPrintArg, renPrintArg, evalExpr_sim hρ r hr n]

theorem execWhile_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env)
      (c : Expr) (body : Block),
    execWhile n ⟨p, m⟩ env c body = execWhile n ⟨p, m'⟩ env (renExpr r c) (renBlock r body)
  | r, _, 0, env, c, body => by simp [execWhile]
  | r, hr, n + 1, env, c, body => by
    simp [execWhile, evalExpr_sim hρ r hr n, execBlock_sim hρ r hr n, execWhile_sim hρ r hr n]

theorem execRange_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env)
      (x : VarId) (t : IntTy) (i hi : Int) (body : Block),
    execRange n ⟨p, m⟩ env x t i hi body = execRange n ⟨p, m'⟩ env x t i hi (renBlock r body)
  | r, _, 0, env, x, t, i, hi, body => by simp [execRange]
  | r, hr, n + 1, env, x, t, i, hi, body => by
    simp [execRange, execBlock_sim hρ r hr n, execRange_sim hρ r hr n]

theorem execEach_sim (hρ : ∀ g c, Resolves m m' ρ (ρ g c) c) :
    ∀ (r : CtxMap) (_hr : ∀ c, Resolves m m' ρ (r c) c) (n : Nat) (env : Env)
      (x : VarId) (idx : Option VarId) (byRef : Bool) (body : Block)
      (vw : ViewVal) (i : Nat),
    execEach n ⟨p, m⟩ env x idx byRef body vw i =
      execEach n ⟨p, m'⟩ env x idx byRef (renBlock r body) vw i
  | r, _, 0, env, x, idx, byRef, body, vw, i => by simp [execEach]
  | r, hr, n + 1, env, x, idx, byRef, body, vw, i => by
    cases idx <;> simp [execEach, execBlock_sim hρ r hr n, execEach_sim hρ r hr n]
end

/-- The globals are initialized alike and the entry runs alike. -/
theorem runModule_sim (hs : Simulates m m' ρ) (fuel : Nat) :
    runModule fuel ⟨p, m⟩ = runModule fuel ⟨p, m'⟩ := by
  unfold runModule
  have entry : enterCall fuel ⟨p, m⟩ 0 m.entry [] = enterCall fuel ⟨p, m'⟩ 0 m'.entry [] := by
    rw [hs.entry]
    exact enterCall_sim hs.bodies fuel 0 m.entry m.entry [] (hs.ids _)
  have glob : ∀ g : GlobalId, (do
        let gl ← lookupGlobal ⟨p, m⟩ g
        let act ← freshAct
        let v ← evalExpr fuel ⟨p, m⟩ ⟨#[], act, [], 0⟩ gl.init
        bindRoot (.global g) v
        (pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit))) = (do
        let gl ← lookupGlobal ⟨p, m'⟩ g
        let act ← freshAct
        let v ← evalExpr fuel ⟨p, m'⟩ ⟨#[], act, [], 0⟩ gl.init
        bindRoot (.global g) v
        (pure (ForInStep.yield PUnit.unit) : M (ForInStep PUnit))) := by
    intro g
    unfold lookupGlobal
    simp only [hs.globals]
    cases m.globals[g]? with
    | none => simp [fault_bind]
    | some gl => simp [evalExpr_sim hs.bodies id hs.ids fuel, renExpr_id]
  simp only [hs.globals, entry, glob]

end Simulation

/-- Executing a module reads only its implementation, context-to-implementation
and global tables and its entry: renaming callees as `Simulates` describes
changes no result, at any fuel and numeric profile. -/
theorem eval_simulates {m m' : Module} {ρ : ImplId → CtxMap} (hs : Simulates m m' ρ)
    (fuel : Nat) (p : NumProfile) : eval fuel p m = eval fuel p m' := by
  unfold eval
  rw [runModule_sim hs fuel]

/-! ### From the quotient relation to the simulation -/

section FromQuotient

variable {m m' : Module} {q : ImplId → ImplId} {ρ : ImplId → CtxMap}

theorem ctxImpl_of_quotient (h : Quotient m m' q ρ) (c : ContextId) :
    (m'.contexts[c]?).map Context.impl = (m.contexts[c]?).map (fun ctx => q ctx.impl) := by
  cases hm : m.contexts[c]? with
  | some ctx => simp [h.contexts c ctx hm]
  | none =>
    have : m'.contexts[c]? = none := by
      rw [Array.getElem?_eq_none_iff] at hm ⊢
      have := h.contextCount; omega
    simp [this]

/-- A context of `m'` that names the implementation `q` sends the implementation
of `c` to resolves like `c` does in `m`, with the callees of the body renamed. -/
theorem resolves_of_quotient (h : Quotient m m' q ρ) (c c' : ContextId)
    (hc : (m'.contexts[c']?).map Context.impl = (m.contexts[c]?).map (fun ctx => q ctx.impl)) :
    Resolves m m' ρ c' c := by
  unfold Resolves resolve resolveIndexed
  cases hm : m.contexts[c]? with
  | none =>
    rw [hm] at hc
    have : m'.contexts[c']? = none := by simpa using hc
    simp [this]
  | some ctx =>
    rw [hm] at hc
    cases hm' : m'.contexts[c']? with
    | none => simp [hm'] at hc
    | some ctx' =>
      rw [hm'] at hc
      have himpl : ctx'.impl = q ctx.impl := Option.some.inj hc
      simp only [Option.bind_some]
      rw [himpl, h.impls c ctx hm]
      cases hh : m.impls[ctx.impl]? <;> simp

theorem simulates_of_quotient (h : Quotient m m' q ρ) : Simulates m m' ρ where
  ids c := resolves_of_quotient h c c (ctxImpl_of_quotient h c)
  bodies g c := by
    apply resolves_of_quotient h
    rw [h.callees g c]
    exact ctxImpl_of_quotient h c
  entry := h.entry
  globals := h.globals

end FromQuotient

/-- **Sharing preserves behaviour.** If `m'` is the quotient of `m` by `q`, with
the callees of each body renamed by `ρ`, then `m` and `m'` give the same result
at every fuel and numeric profile. Fuel is the only recursion, so a call cycle
through several implementations needs no separate argument: each call consumes
one unit. -/
theorem share_eval {m m' : Module} {q : ImplId → ImplId} {ρ : ImplId → CtxMap}
    (h : Quotient m m' q ρ) (fuel : Nat) (p : NumProfile) :
    eval fuel p m = eval fuel p m' :=
  eval_simulates (simulates_of_quotient h) fuel p

/-- The relation stated for every implementation: each implementation of `m` reappears,
renamed, at its mapped index of `m'`. With every context naming an
implementation that exists, this is the relation `Quotient` states for the
implementations contexts name, so it implies it. -/
theorem quotient_of_implwise {m m' : Module} {q : ImplId → ImplId} {ρ : ImplId → CtxMap}
    (files : m'.files = m.files) (types : m'.types = m.types)
    (origins : m'.origins = m.origins) (entry : m'.entry = m.entry)
    (globals : m'.globals = m.globals) (contextCount : m'.contexts.size = m.contexts.size)
    (contexts : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
      m'.contexts[c]? = some { ctx with impl := q ctx.impl })
    (inRange : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
      ctx.impl < m.impls.size)
    (impls : ∀ (f : ImplId) (i : Impl), m.impls[f]? = some i →
      m'.impls[q f]? = some (renImpl (ρ f) i))
    (callees : ∀ (f : ImplId) (c : ContextId),
      (m'.contexts[ρ f c]?).map Context.impl = (m'.contexts[c]?).map Context.impl) :
    Quotient m m' q ρ where
  files := files
  types := types
  origins := origins
  entry := entry
  globals := globals
  contextCount := contextCount
  contexts := contexts
  impls c ctx hm := by
    have hlt := inRange c ctx hm
    rw [Array.getElem?_eq_getElem hlt]
    simpa using impls ctx.impl _ (Array.getElem?_eq_getElem hlt)
  callees := callees

/-- **A quotient of a module that never faults never faults.** -/
theorem share_never_faults {m m' : Module} {q : ImplId → ImplId} {ρ : ImplId → CtxMap}
    (h : Quotient m m' q ρ) (safe : ∀ n p k, eval n p m ≠ .fault k) :
    ∀ n p k, eval n p m' ≠ .fault k := by
  intro n p k
  rw [← share_eval h n p]
  exact safe n p k

/-- The composition with the safety theorem, which is taken as a hypothesis:
a validated module's quotient never faults. -/
theorem share_validated_never_faults
    (safety : ∀ m : Module, validate m = .ok () → ∀ n p k, eval n p m ≠ .fault k)
    {m m' : Module} {q : ImplId → ImplId} {ρ : ImplId → CtxMap}
    (h : Quotient m m' q ρ) (valid : validate m = .ok ()) :
    ∀ n p k, eval n p m' ≠ .fault k :=
  share_never_faults h (safety m valid)

/-! ### Erasing the root annotations -/

theorem renImpl_id (i : Impl) : renImpl id i = i := by
  simp [renImpl, renBlock_id]

/-- **`eval` ignores root annotations.** A module that has the same
implementations, globals and entry, and whose contexts name the same
implementations, gives the same result at every fuel and numeric profile. The
erased fields are every field of a context other than `impl`: the declaration
key and the root sets of variables and results. -/
theorem eval_erase_roots {m m' : Module}
    (himpls : m'.impls = m.impls) (hglobals : m'.globals = m.globals)
    (hentry : m'.entry = m.entry)
    (hctx : ∀ c : ContextId, (m'.contexts[c]?).map Context.impl = (m.contexts[c]?).map Context.impl)
    (fuel : Nat) (p : NumProfile) : eval fuel p m = eval fuel p m' := by
  have res : ∀ c, resolve m' c = resolve m c := by
    intro c
    unfold resolve
    cases hm : m.contexts[c]? with
    | none =>
      have : m'.contexts[c]? = none := by simpa [hm] using hctx c
      simp [this]
    | some ctx =>
      cases hm' : m'.contexts[c]? with
      | none => have := hctx c; simp [hm, hm'] at this
      | some ctx' =>
        have := hctx c
        simp only [hm, hm', Option.map_some, Option.some.injEq] at this
        simp [this, himpls]
  have res' : ∀ c, Resolves m m' (fun _ => id) c c := by
    intro c
    unfold Resolves
    rw [res, resolve_eq_map_snd]
    cases resolveIndexed m c <;> simp [renImpl_id]
  exact eval_simulates (ρ := fun _ => id)
    { ids := res', bodies := fun _ c => res' c, entry := hentry, globals := hglobals } fuel p

theorem eval_eraseRoots (m : Module) (fuel : Nat) (p : NumProfile) :
    eval fuel p (eraseRoots m) = eval fuel p m := by
  symm
  exact eval_erase_roots (m := m) (m' := eraseRoots m) rfl rfl rfl
    (fun c => by simp only [eraseRoots, Array.getElem?_map]; cases m.contexts[c]? <;> rfl) fuel p

/-! ### Soundness of the executable check -/

theorem eqImpl_sound {a b : Impl} (h : eqImpl a b = true) : a = b := by
  obtain ⟨n, ps, rs, vs, body, sm⟩ := a
  obtain ⟨n', ps', rs', vs', body', sm'⟩ := b
  simp only [eqImpl, eqSummary, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have := eqBlock_sound _ _ h5
  simp_all

theorem eqGlobal_sound {a b : Global} (h : eqGlobal a b = true) : a = b := by
  obtain ⟨n, t, k, i, o⟩ := a
  obtain ⟨n', t', k', i', o'⟩ := b
  simp only [eqGlobal, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have := eqExpr_sound _ _ h4
  simp_all

theorem allZip_sound {α β : Type} (f : α → β → Bool) (g : α → β)
    (hf : ∀ a b, f a b = true → b = g a) :
    ∀ (as : List α) (bs : List β), allZip f as bs = true → bs = as.map g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [allZip] at h
  | _ :: _, [], h => by simp [allZip] at h
  | a :: as, b :: bs, h => by
    simp only [allZip, Bool.and_eq_true] at h
    have := hf _ _ h.1
    have := allZip_sound f g hf as bs h.2
    simp_all

theorem eqOptImpl_sound {a b : Option Impl} (h : eqOptImpl a b = true) : a = b := by
  cases a <;> cases b <;> simp [eqOptImpl] at h ⊢
  exact eqImpl_sound h

/-- **The checker is sound.** If it accepts `m'` as the quotient of `m` under
the witnesses `qt` and `rt`, then `m'` is that quotient, with each body kept or
renamed by `rt`, so `m` and `m'` behave alike at every fuel (`share_eval`). -/
theorem checkQuotient_sound {m m' : Module} {qt : Array ImplId} {rt : Array ContextId}
    (h : checkQuotient m m' qt rt = true) :
    Quotient m m' (fun f => qt.getD f f) (bodyRenaming m m' (fun f => qt.getD f f) rt) := by
  simp only [checkQuotient, headerOk, contextsOk, implsOk, calleesOk,
    Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hfiles, htypes, horigins, hentry, hglobals, hctxs, himpls, hrt, hcallees⟩ := h
  have gl := allZip_sound _ id (fun a b hab => (eqGlobal_sound hab).symm) _ _ hglobals
  have cx := allZip_sound _ (fun ctx : Context => { ctx with impl := qt.getD ctx.impl ctx.impl })
    (fun a b hab => by simpa using hab) _ _ hctxs
  have cxs : m'.contexts.toList = m.contexts.toList.map
      (fun ctx : Context => { ctx with impl := qt.getD ctx.impl ctx.impl }) := cx
  refine
    { files := hfiles, types := htypes, origins := horigins, entry := hentry
      globals := ?_, contextCount := ?_, contexts := ?_, impls := ?_, callees := ?_ }
  · apply Array.ext'
    simpa using gl
  · have := congrArg List.length cxs
    simpa using this
  · intro c ctx hm
    have e1 : m.contexts.toList[c]? = some ctx := by simpa using hm
    have e2 : m'.contexts.toList[c]? = some { ctx with impl := qt.getD ctx.impl ctx.impl } := by
      rw [cxs]; simp [e1]
    simpa using e2
  · intro c ctx hm
    have mem : ctx ∈ m.contexts.toList := by
      have e1 : m.contexts.toList[c]? = some ctx := by simpa using hm
      exact List.mem_of_getElem? e1
    have := (List.all_eq_true.mp himpls) ctx mem
    unfold bodyRenaming
    by_cases hk : keepsBody m m' (fun f => qt.getD f f) ctx.impl = true
    · simp only [hk, ite_true]
      have := eqOptImpl_sound hk
      rw [this]
      cases m.impls[ctx.impl]? <;> simp [renImpl_id]
    · simp only [hk]
      simp only [Bool.not_eq_true] at hk
      simp only [hk, Bool.false_or] at this
      exact eqOptImpl_sound this
  · intro f c
    by_cases hk : keepsBody m m' (fun f => qt.getD f f) f = true
    · have : bodyRenaming m m' (fun f => qt.getD f f) rt f = id := by
        unfold bodyRenaming; simp only [hk, ↓reduceIte]
      rw [this]; rfl
    · have : bodyRenaming m m' (fun f => qt.getD f f) rt f = fun c => rt.getD c c := by
        unfold bodyRenaming; simp only [hk, Bool.false_eq_true, ↓reduceIte]
      rw [this]
      by_cases hc : c < m.contexts.size
      · have := (List.all_eq_true.mp hcallees) c (List.mem_range.mpr hc)
        simpa using this
      · have hrc : rt.getD c c = c := by
          have : rt.size ≤ c := hrt ▸ Nat.le_of_not_lt hc
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none this]
        simp [hrc]

end Goose.Proofs.Share
