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

variable {p : NumProfile} {m m' : Module} {r : CtxMap}

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

mutual
theorem evalExpr_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (e : Expr),
    evalExpr n ⟨p, m⟩ env e = evalExpr n ⟨p, m'⟩ env (renExpr r e)
  | 0, env, e => by simp [evalExpr]
  | n + 1, env, e => by
    cases e with
    | call c args o =>
      simp only [evalExpr, renExpr, renArgs_eq_map]
      rw [mapM_sim _ (evalArg n ⟨p, m'⟩ env) (renArg r) (fun a => evalArg_sim hs n env a)]
      have call : ∀ depth c vals, enterCall n ⟨p, m⟩ depth c vals =
          enterCall n ⟨p, m'⟩ depth (r c) vals :=
        fun depth c vals => enterCall_sim hs n depth c (r c) vals (hs.resolves c)
      simp only [call]
    | arrLit t es =>
      simp only [evalExpr, renExpr, renExprs_eq_map]
      rw [mapM_sim _ (evalExpr n ⟨p, m'⟩ env) (renExpr r) (fun a => evalExpr_sim hs n env a)]
    | _ => simp [evalExpr, renExpr, evalExpr_sim hs n, evalPlace_sim hs n, evalView_sim hs n,
        evalBound_sim hs n, blockValue_sim hs n]

theorem blockValue_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (b : Block),
    blockValue n ⟨p, m⟩ env b = blockValue n ⟨p, m'⟩ env (renBlock r b)
  | 0, env, b => by simp [blockValue]
  | n + 1, env, b => by simp [blockValue, execBlock_sim hs n]

theorem evalArg_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (a : Arg),
    evalArg n ⟨p, m⟩ env a = evalArg n ⟨p, m'⟩ env (renArg r a)
  | 0, env, a => by simp [evalArg]
  | n + 1, env, a => by
    cases a <;> simp [evalArg, renArg, evalExpr_sim hs n, evalPlace_sim hs n]

theorem evalBound_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (env : Env) (len : Nat) (dflt : Int) (b : Bound),
    evalBound n ⟨p, m⟩ env len dflt b = evalBound n ⟨p, m'⟩ env len dflt (renBound r b)
  | 0, env, len, dflt, b => by simp [evalBound]
  | n + 1, env, len, dflt, b => by
    cases b <;> simp [evalBound, renBound, evalExpr_sim hs n]

theorem evalPlace_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (pl : Place),
    evalPlace n ⟨p, m⟩ env pl = evalPlace n ⟨p, m'⟩ env (renPlace r pl)
  | 0, env, pl => by simp [evalPlace]
  | n + 1, env, pl => by
    cases pl <;> simp [evalPlace, renPlace, evalExpr_sim hs n, evalView_sim hs n]

theorem evalView_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (v : View),
    evalView n ⟨p, m⟩ env v = evalView n ⟨p, m'⟩ env (renView r v)
  | 0, env, v => by simp [evalView]
  | n + 1, env, v => by
    cases v <;> simp [evalView, renView, evalExpr_sim hs n, evalPlace_sim hs n]

theorem enterCall_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (depth : Nat) (c c' : ContextId) (vals : List Val),
    resolve m' c' = (resolve m c).map (renImpl r) →
    enterCall n ⟨p, m⟩ depth c vals = enterCall n ⟨p, m'⟩ depth c' vals
  | 0, depth, c, c', vals, _ => by simp [enterCall]
  | n + 1, depth, c, c', vals, hc => by
    simp only [enterCall, lookup_chain, hc]
    cases resolve m c with
    | none => rfl
    | some i => simp [renImpl, execBlock_sim hs n]

theorem execBlock_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (env : Env) (pre : List (VarId × Val)) (b : Block),
    execBlock n ⟨p, m⟩ env pre b = execBlock n ⟨p, m'⟩ env pre (renBlock r b)
  | 0, env, pre, b => by simp [execBlock]
  | n + 1, env, pre, .mk sc stmts value => by
    cases value with
    | none => simp [execBlock, renBlock, renOptExpr, execStmts_sim hs n]
    | some e =>
      simp only [execBlock, renBlock, renOptExpr, execStmts_sim hs n]
      congr 1; funext si; congr 1; funext fl; congr 1; funext flow
      cases flow <;> simp [evalExpr_sim hs n]

theorem execStmts_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (ss : List Stmt),
    execStmts n ⟨p, m⟩ env ss = execStmts n ⟨p, m'⟩ env (renStmts r ss)
  | 0, env, ss => by simp [execStmts]
  | n + 1, env, [] => by simp [execStmts, renStmts]
  | n + 1, env, s :: rest => by
    simp [execStmts, renStmts, execStmt_sim hs n, execStmts_sim hs n]

theorem execStmt_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (s : Stmt),
    execStmt n ⟨p, m⟩ env s = execStmt n ⟨p, m'⟩ env (renStmt r s)
  | 0, env, s => by simp [execStmt]
  | n + 1, env, s => by
    cases s with
    | print args o =>
      simp only [execStmt, renStmt, renPrintArgs_eq_map]
      rw [mapM_sim _ (execPrintArg n ⟨p, m'⟩ env) (renPrintArg r) (fun a => execPrintArg_sim hs n env a)]
    | ifS c t f o =>
      cases f <;> simp [execStmt, renStmt, renOptBlock, evalExpr_sim hs n, execBlock_sim hs n]
    | ret e o => cases e <;> simp [execStmt, renStmt, renOptExpr, evalExpr_sim hs n]
    | _ => simp [execStmt, renStmt, evalExpr_sim hs n, evalPlace_sim hs n, evalView_sim hs n,
        execWhile_sim hs n, execRange_sim hs n, execEach_sim hs n]

theorem execPrintArg_sim (hs : Simulates m m' r) : ∀ (n : Nat) (env : Env) (a : PrintArg),
    execPrintArg n ⟨p, m⟩ env a = execPrintArg n ⟨p, m'⟩ env (renPrintArg r a)
  | 0, env, a => by simp [execPrintArg]
  | n + 1, env, a => by
    cases a <;> simp [execPrintArg, renPrintArg, evalExpr_sim hs n]

theorem execWhile_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (env : Env) (c : Expr) (body : Block),
    execWhile n ⟨p, m⟩ env c body = execWhile n ⟨p, m'⟩ env (renExpr r c) (renBlock r body)
  | 0, env, c, body => by simp [execWhile]
  | n + 1, env, c, body => by
    simp [execWhile, evalExpr_sim hs n, execBlock_sim hs n, execWhile_sim hs n]

theorem execRange_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (env : Env) (x : VarId) (t : IntTy) (i hi : Int) (body : Block),
    execRange n ⟨p, m⟩ env x t i hi body = execRange n ⟨p, m'⟩ env x t i hi (renBlock r body)
  | 0, env, x, t, i, hi, body => by simp [execRange]
  | n + 1, env, x, t, i, hi, body => by
    simp [execRange, execBlock_sim hs n, execRange_sim hs n]

theorem execEach_sim (hs : Simulates m m' r) :
    ∀ (n : Nat) (env : Env) (x : VarId) (idx : Option VarId) (byRef : Bool) (body : Block)
      (vw : ViewVal) (i : Nat),
    execEach n ⟨p, m⟩ env x idx byRef body vw i =
      execEach n ⟨p, m'⟩ env x idx byRef (renBlock r body) vw i
  | 0, env, x, idx, byRef, body, vw, i => by simp [execEach]
  | n + 1, env, x, idx, byRef, body, vw, i => by
    cases idx <;> simp [execEach, execBlock_sim hs n, execEach_sim hs n]
end

/-- The globals are initialized alike and the entry runs alike. -/
theorem runModule_sim (hs : Simulates m m' r) (fuel : Nat) :
    runModule fuel ⟨p, m⟩ = runModule fuel ⟨p, m'⟩ := by
  unfold runModule
  have entry : enterCall fuel ⟨p, m⟩ 0 m.entry [] = enterCall fuel ⟨p, m'⟩ 0 m'.entry [] :=
    enterCall_sim hs fuel 0 m.entry m'.entry [] hs.entry
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
    have hg := hs.globalInit g
    unfold lookupGlobal
    cases h : m.globals[g]? with
    | none => simp_all [fault_bind]
    | some gl =>
      cases h' : m'.globals[g]? with
      | none => simp_all
      | some gl' =>
        simp only [h, h', Option.map_some] at hg ⊢
        have : gl'.init = renExpr r gl.init := Option.some.inj hg
        simp [this, evalExpr_sim hs fuel]
  simp only [hs.globalCount, entry, glob]

end Simulation

/-- Executing a module reads only its implementation, context-to-implementation
and global tables and its entry: renaming callees as `Simulates` describes
changes no result, at any fuel and numeric profile. -/
theorem eval_simulates {m m' : Module} {r : CtxMap} (hs : Simulates m m' r)
    (fuel : Nat) (p : NumProfile) : eval fuel p m = eval fuel p m' := by
  unfold eval
  rw [runModule_sim hs fuel]


/-! ### From the quotient relation to the simulation -/

section FromQuotient

variable {m m' : Module} {q : ImplId → ImplId} {r : CtxMap}

theorem ctxImpl_of_quotient (h : Quotient m m' q r) (c : ContextId) :
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
theorem resolve_of_quotient (h : Quotient m m' q r) (c c' : ContextId)
    (hc : (m'.contexts[c']?).map Context.impl = (m.contexts[c]?).map (fun ctx => q ctx.impl)) :
    resolve m' c' = (resolve m c).map (renImpl r) := by
  unfold resolve
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
      simp [himpl, h.impls c ctx hm]

theorem simulates_of_quotient (h : Quotient m m' q r) : Simulates m m' r where
  resolves c := by
    apply resolve_of_quotient h
    rw [h.callees c]
    exact ctxImpl_of_quotient h c
  entry := by
    rw [h.entry]
    exact resolve_of_quotient h _ _ (ctxImpl_of_quotient h _)
  globalCount := by simp [h.globals]
  globalInit g := by
    rw [h.globals]
    cases hg : m.globals[g]? <;> simp_all [renGlobal]

end FromQuotient

/-- **Sharing preserves behaviour.** If `m'` is the quotient of `m` by `q` with
callees renamed by `r`, then `m` and `m'` give the same result at every fuel and
numeric profile. Fuel is the only recursion, so a call cycle through several
implementations needs no separate argument: each call consumes one unit. -/
theorem share_eval {m m' : Module} {q : ImplId → ImplId} {r : CtxMap}
    (h : Quotient m m' q r) (fuel : Nat) (p : NumProfile) :
    eval fuel p m = eval fuel p m' :=
  eval_simulates (simulates_of_quotient h) fuel p

/-- **A quotient of a module that never faults never faults.** -/
theorem share_never_faults {m m' : Module} {q : ImplId → ImplId} {r : CtxMap}
    (h : Quotient m m' q r) (safe : ∀ n p k, eval n p m ≠ .fault k) :
    ∀ n p k, eval n p m' ≠ .fault k := by
  intro n p k
  rw [← share_eval h n p]
  exact safe n p k

/-- The composition with the safety theorem, which is taken as a hypothesis:
a validated module's quotient never faults. -/
theorem share_validated_never_faults
    (safety : ∀ m : Module, validate m = .ok () → ∀ n p k, eval n p m ≠ .fault k)
    {m m' : Module} {q : ImplId → ImplId} {r : CtxMap}
    (h : Quotient m m' q r) (valid : validate m = .ok ()) :
    ∀ n p k, eval n p m' ≠ .fault k :=
  share_never_faults h (safety m valid)

/-! ### Erasing the root annotations -/

theorem renImpl_id (i : Impl) : renImpl id i = i := by
  simp [renImpl, renBlock_id]

theorem renGlobal_id (g : Global) : renGlobal id g = g := by
  simp [renGlobal, renExpr_id]

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
  have mapid : ∀ o : Option Impl, o.map (renImpl id) = o := by
    intro o; cases o <;> simp [renImpl_id]
  apply eval_simulates (r := id)
  exact
    { resolves := fun c => by simp [res, mapid]
      entry := by simp [res, mapid, hentry]
      globalCount := by simp [hglobals]
      globalInit := fun g => by simp [hglobals, renExpr_id] }

/-- The module with every context's declaration key and root annotations
removed. -/
def eraseRoots (m : Module) : Module :=
  { m with contexts := m.contexts.map fun c =>
      { impl := c.impl, decl := "", varRoots := [], resultRoots := [] } }

theorem eval_eraseRoots (m : Module) (fuel : Nat) (p : NumProfile) :
    eval fuel p (eraseRoots m) = eval fuel p m := by
  symm
  exact eval_erase_roots (m := m) (m' := eraseRoots m) rfl rfl rfl
    (fun c => by simp only [eraseRoots, Array.getElem?_map]; cases m.contexts[c]? <;> rfl) fuel p

end Goose.Proofs.Share
