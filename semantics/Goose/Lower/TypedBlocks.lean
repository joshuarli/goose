import Goose.Lower.SourceContexts
import Goose.Lower.LoopBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

def LoopSourceMatches (typingEnv : TEnv) (loop : Option LoopCtx) : Prop :=
  loop = none ↔ typingEnv.loops = 0

theorem LoopSourceMatches.transport {before after : TEnv} {loop : Option LoopCtx}
    (h : LoopSourceMatches before loop) (hloops : after.loops = before.loops) :
    LoopSourceMatches after loop := by
  unfold LoopSourceMatches at h ⊢
  rw [hloops]
  exact h

def TypedStatementLoopSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (stmt : Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env stmt state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls ls' : LS) (result : Unit) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt loop stmt (lowerEnv cfg.mod env.vars results) ls = (result, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr →
    SimEAt cx pt fr (execStmt n cfg env stmt >>= prepareLoopFlow env loop)
      (StatementLoopPost cfg env cx ls fr ls' loop) state

def TypedStatementsLoopSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (stmts : List Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtsSource cfg env stmts state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls ls' : LS) (result : Unit) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts loop stmts (lowerEnv cfg.mod env.vars results) ls = (result, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr →
    SimEAt cx pt fr (execStmts n cfg env stmts >>= prepareLoopFlow env loop)
      (StatementLoopPost cfg env cx ls fr ls' loop) state

theorem typedStatementsLoopSimulation_zero (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (stmts : List Stmt) :
    TypedStatementsLoopSimulation 0 cfg results loop stmts := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  simp only [execStmts]
  exact SimEAt.of_simG SimG.of_timeout_bind state

theorem typedStatementsLoopSimulation_nil (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) : TypedStatementsLoopSimulation n cfg results loop [] := by
  cases n with
  | zero => exact typedStatementsLoopSimulation_zero cfg results loop []
  | succ n =>
    intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
      hgir hresults hdepth htargets hcounter
    simp only [lowerStmts, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    cases loop <;>
      simp only [execStmts, prepareLoopFlow, prepareReturn, prepareLoopExit, pure_bind] <;>
      exact SimEAt.ret (Or.inl ⟨rfl, Post.init hrel hpp⟩)

theorem BlockSource.preScopes {cfg : Cfg} {env : Env} {pre : List (SlotId × ValueId × OriginId)}
    {pre' : List (VarId × Val)} {block : Core.Block} {state : St} {fr : GIR.Frame}
    (source : BlockSource cfg env pre' block state) (hpre : PreRel fr pre pre') :
    ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = block.scope := by
  intro p hp
  obtain ⟨value, hvalue⟩ := hpre.source_member p hp
  obtain ⟨_, _, lv, hvar, hscope, _⟩ := source.pretyped.2 p.1 value hvalue
  exact ⟨lv, hvar, hscope⟩

theorem LoopCounterAt.sameValues {loop : Option LoopCtx} {ls ls' : LS}
    {fr fr' : GIR.Frame} (h : LoopCounterAt loop ls fr)
    (hvalues : fr'.vals = fr.vals) (hfrontier : ls'.vals.size = ls.vals.size) :
    LoopCounterAt loop ls' fr' := by
  cases loop with
  | none => trivial
  | some context =>
    cases hkind : context.cont with
    | jump header => simp [LoopCounterAt, hkind]
    | next header hint counter =>
      simp only [LoopCounterAt, hkind] at h ⊢
      rw [hvalues, hfrontier]
      exact h

theorem loopDepthFits_entered {env : Env} {loop : Option LoopCtx}
    (scope : ScopeId) (si : ScopeInst) (h : LoopDepthFits env loop) :
    LoopDepthFits { env with scopes := (scope, si) :: env.scopes } loop := by
  cases loop with
  | none => trivial
  | some context =>
    change context.depth ≤ env.scopes.length + 1
    exact Nat.le_trans h (Nat.le_succ _)

theorem SourceResults.transport {before after : TEnv} {rootsBefore rootsAfter : PEnv}
    {results : List Ty} (h : SourceResults before rootsBefore results)
    (htyping : after.impl = before.impl) (hroots : rootsAfter.impl = rootsBefore.impl) :
    SourceResults after rootsAfter results := by
  intro impl himpl
  obtain ⟨hroot, hresults⟩ := h impl (htyping.symm.trans himpl)
  exact ⟨hroots.trans hroot, hresults⟩

def TypedBlockLoopSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (block : Core.Block) : Prop :=
  ∀ (env : Env) (state : St) (source : BlockSource cfg env pre' block state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls ls' : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock loop pre want block (lowerEnv cfg.mod env.vars results) ls = (result, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr →
    SimEAt cx pt fr (execBlock n cfg env pre' block >>= prepareLoopFlow env loop)
      (BlockLoopPost cfg env cx ls fr ls' loop block want result) state

theorem BlockLoopPost.none {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS}
    {before after : GIR.Frame} {block : Core.Block} {want : Bool} {result : ValueId}
    {flow : Flow} {pt : Pt} :
    BlockLoopPost cfg env cx ls before ls' none block want result flow pt after ↔
      BlockFlowPost cfg env cx ls before ls' block want result flow pt after := by
  simp [BlockLoopPost, BlockFlowPost]

theorem TypedBlockLoopSimulation.function {n : Nat} {cfg : Cfg} {results : List Ty}
    {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)}
    {want : Bool} {block : Core.Block}
    (h : TypedBlockLoopSimulation n cfg results none pre pre' want block)
    (env : Env) (state : St) (source : BlockSource cfg env pre' block state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hloops : source.typingEnv.loops = 0)
    (ls ls' : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerBlock none pre want block (lowerEnv cfg.mod env.vars results) ls = (result, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hpre : PreRel fr pre pre') (hgir : cx.cfg.mod = lower cfg.mod)
    (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execBlock n cfg env pre' block >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' block want result) state := by
  have halign : LoopSourceMatches source.typingEnv none := by
    exact ⟨fun _ => hloops, fun _ => rfl⟩
  have hs := h env state source hmetadata halign ls ls' result pt cx fr hlow hpp hext hrel hpre
    hgir hresults trivial trivial trivial
  rw [prepareLoopFlow_none] at hs
  exact hs.mono fun flow _ pt' fr' _ hp => BlockLoopPost.none.mp hp

theorem typedBlockLoopSimulation_zero (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (block : Core.Block) :
    TypedBlockLoopSimulation 0 cfg results loop pre pre' want block := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel hpre
    hgir hresults hdepth htargets hcounter
  simp only [execBlock]
  exact SimEAt.of_simG SimG.of_timeout_bind state

theorem typedBlockLoopSimulation_succ (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (scope : ScopeId)
    (stmts : List Stmt) (value : Option Expr)
    (hstmts : TypedStatementsLoopSimulation n cfg results loop stmts)
    (hvalue : match value with | none => True | some expr => TypedExprClaim n cfg results expr) :
    TypedBlockLoopSimulation (n + 1) cfg results loop pre pre' want (.mk scope stmts value) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel hpre
    hgir hresults hdepth htargets hcounter
  obtain ⟨ls1, ls_p, ls_s, ls_x, ls_l, u0, u, rx, h1, h2, h3, h4, h5, hls', hr⟩ :=
    prefixBlock_unfold hlow
  rw [prepareLoopFlow_execBlock _ _ _ _ _ _ _ _ hdepth]
  refine preparedLoopBlock_core_at (source.preScopes hpre) h1 h2 h3 h4 h5 hls' hr
    hpp hext hrel hpre hdepth ?_ ?_
  · intro si entered initialized hfresh hbind pt_s fr_s hpp_s hext_s hrel_s hvalues hfrontier
    change Res.ok state.nextScope { state with nextScope := state.nextScope + 1 } =
      .ok si entered at hfresh
    obtain ⟨rfl, rfl⟩ := Res.ok.inj hfresh
    rw [Core.Sound.bindAll_eq] at hbind
    obtain ⟨_, rfl⟩ := Res.ok.inj hbind
    obtain ⟨statements, htyping, hfinal, hroots, _⟩ := source.enter
    have hmeta : SourceResults statements.typingEnv statements.rootsEnv results := by
      apply hmetadata.transport
      · rw [htyping]
        exact source.same.impl
      · rw [hroots]
    have halign : LoopSourceMatches statements.typingEnv loop := by
      apply hloops.transport
      rw [htyping]
      exact source.same.loops
    exact hstmts _ _ statements hmeta halign ls_p ls_s u pt_s cx fr_s h3 hpp_s hext_s hrel_s
      hgir hresults (loopDepthFits_entered scope _ hdepth) htargets
      (hcounter.sameValues hvalues hfrontier)
  · intro si entered initialized after hfresh hbind hactual pt_x fr_x hpp_x hext_x hrel_x
    change Res.ok state.nextScope { state with nextScope := state.nextScope + 1 } =
      .ok si entered at hfresh
    obtain ⟨rfl, rfl⟩ := Res.ok.inj hfresh
    rw [Core.Sound.bindAll_eq] at hbind
    obtain ⟨_, rfl⟩ := Res.ok.inj hbind
    obtain ⟨statements, htyping, hfinal, hroots, hworld, hobservation, htypingStart,
      htypingEnd, hrootsStart, hrootsEnd, hplans, hpath, hcontext, hall, hblockValue, hoffset⟩ :=
      source.enter
    have hraw := preparedLoopFlow_normal_success hactual
    cases value with
    | some expr =>
      have htv : tyExpr statements.typingAfter expr statements.typingEnd =
          .ok (source.ty, source.typingEnd) := by
        rw [hfinal, htypingEnd]
        exact source.typedValue
      have hrv : rpExpr statements.rootsEnv expr statements.rootsEnd =
          .ok (source.roots, source.rootsEnd) := by
        rw [hroots, hrootsEnd]
        exact source.rootedValue
      have heffects : Core.Sound.EffLe source.rootsEnd.eff statements.world.E := by
        rw [hworld]
        exact source.effects
      obtain ⟨child, hchildTyping, hchildRoots, hchildTy⟩ := statements.valueChild expr
        hblockValue source.ty source.typingEnd source.roots source.rootsEnd htv hrv heffects
        n .unit hraw
      obtain ⟨finalTyping, same, frame, hnormal⟩ := (statements.result n (.normal .unit) hraw).frame
      have hfinalTyping := hnormal .unit rfl
      subst finalTyping
      have hmeta : SourceResults child.typingEnv child.rootsEnv results := by
        apply hmetadata.transport
        · rw [hchildTyping, same.impl, htyping]
          exact source.same.impl
        · rw [hchildRoots, hroots]
      simp only [lowerBlockValue] at h4
      simp only [valueFlow]
      refine SimEAt.bind (hvalue _ _ child hmeta ls_s ls_x rx pt_x cx fr_x h4 hpp_x hext_x
        hrel_x hgir hresults) fun v _ pt' fr' _ P => ?_
      exact SimEAt.ret ⟨v, rfl, (fun h => by cases h), by
        simpa only [blockCells, Core.Block.value, Core.Block.scope, Option.isSome_some, Bool.true_or,
          ↓reduceIte] using P⟩
    | none =>
      cases want with
      | false =>
        simp only [lowerBlockValue, pure_run] at h4
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
        exact SimEAt.ret ⟨.unit, rfl, (fun _ => rfl), by
          simpa only [blockCells, Core.Block.value, Option.isSome_none, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte] using Post.init hrel_x hpp_x⟩
      | true =>
        simp only [lowerBlockValue] at h4
        change SimEAt cx pt_x fr_x ((pure () : M Unit) >>= fun _ => pure (Flow.normal .unit)) _ after
        refine SimEAt.bind (SimEAt.of_simG (leaf_def (Post.init hrel_x hpp_x) h4 hext_x
          (by simp) (fun _ => RVal.val Val.unit) (c := (pure () : M Unit))
          (by simp [execPure])) after) fun _ _ pt' fr' _ P => ?_
        exact SimEAt.ret ⟨.unit, rfl, (fun _ => rfl), by
          simpa only [blockCells, Core.Block.value, Option.isSome_none, Bool.false_or,
            Bool.or_true, ↓reduceIte] using P⟩

theorem typedBlockLoopSimulation_nil (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (scope : ScopeId) :
    TypedBlockLoopSimulation n cfg results loop pre pre' want (.mk scope [] none) := by
  cases n with
  | zero => exact typedBlockLoopSimulation_zero cfg results loop pre pre' want _
  | succ n =>
    exact typedBlockLoopSimulation_succ n cfg results loop pre pre' want scope [] none
      (typedStatementsLoopSimulation_nil n cfg results loop) trivial

end Goose.Lower
