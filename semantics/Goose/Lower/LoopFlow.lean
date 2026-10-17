import Goose.Lower.FlowState
import Goose.Lower.LoopExit

namespace Goose.Lower

open Goose.Core Goose.GIR

structure LoopTargets (fn : Func) (loop : LoopCtx) : Prop where
  breakBlock : ∃ block, fn.blocks[loop.breakTo]? = some block ∧ block.params = []
  continueBlock : match loop.cont with
    | .jump header => ∃ block, fn.blocks[header]? = some block ∧ block.params = []
    | .next header hint counter => ∃ block, fn.blocks[header]? = some block ∧
        block.params = [(counter, .data (.int hint))]

structure LoopFramePost (before : GIR.Frame) (frontier : ValueId)
    (scopes : List (ScopeId × ScopeInst)) (after : GIR.Frame) : Prop where
  values : Same frontier before after
  activation : after.act = before.act
  scopesEqual : after.scopes = scopes
  depth : after.depth = before.depth

def ExitedAt (loop : LoopCtx) (before : GIR.Frame) (frontier : ValueId)
    (scopes : List (ScopeId × ScopeInst)) (pt : Pt) (after : GIR.Frame) : Prop :=
  pt = (loop.breakTo, 0) ∧ LoopFramePost before frontier scopes after

def ContinuedAt (loop : LoopCtx) (before : GIR.Frame) (frontier : ValueId)
    (scopes : List (ScopeId × ScopeInst)) (pt : Pt) (after : GIR.Frame) : Prop :=
  match loop.cont with
  | .jump header => pt = (header, 0) ∧ LoopFramePost before frontier scopes after
  | .next header _ counter => ∃ runtimeTy current,
      before.vals[counter]? = some (.val (.int runtimeTy current)) ∧
      NextJumpPost before header counter runtimeTy current scopes pt after

def LoopFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (loop : LoopCtx) (block : Core.Block) (result : ValueId)
    (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (∃ value, flow = .normal value ∧
    Post cfg env cx ls fr ls' fr' pt' (blockCells block false result value)) ∨
  ReturnedAt cx flow pt' fr' ∨
  (flow = .brk ∧ ExitedAt loop fr ls.vals.size env.scopes pt' fr') ∨
  (flow = .cont ∧ ContinuedAt loop fr ls.vals.size env.scopes pt' fr')

theorem JumpPost.loopFrame {before after : GIR.Frame} {target : BlockId}
    {scopes : List (ScopeId × ScopeInst)} {pt : Pt} (h : JumpPost before target scopes pt after)
    (frontier : ValueId) : LoopFramePost before frontier scopes after :=
  ⟨fun id _ => by rw [h.values], h.activation, h.scopesEqual, h.depth⟩

theorem JumpPost.exitedAt {loop : LoopCtx} {before after : GIR.Frame}
    {scopes : List (ScopeId × ScopeInst)} {pt : Pt}
    (h : JumpPost before loop.breakTo scopes pt after) (frontier : ValueId) :
    ExitedAt loop before frontier scopes pt after := ⟨h.point, h.loopFrame frontier⟩

theorem JumpPost.continuedAt {loop : LoopCtx} {header : BlockId} {before after : GIR.Frame}
    {scopes : List (ScopeId × ScopeInst)} {pt : Pt}
    (hkind : loop.cont = .jump header) (h : JumpPost before header scopes pt after)
    (frontier : ValueId) : ContinuedAt loop before frontier scopes pt after := by
  rw [ContinuedAt, hkind]
  exact ⟨h.point, h.loopFrame frontier⟩

theorem NextJumpPost.continuedAt {loop : LoopCtx} {header : BlockId} {hint runtimeTy : IntTy}
    {counter frontier : ValueId} {current : Int} {before after : GIR.Frame}
    {scopes : List (ScopeId × ScopeInst)} {pt : Pt}
    (hkind : loop.cont = .next header hint counter)
    (hcell : before.vals[counter]? = some (.val (.int runtimeTy current)))
    (h : NextJumpPost before header counter runtimeTy current scopes pt after) :
    ContinuedAt loop before frontier scopes pt after := by
  rw [ContinuedAt, hkind]
  exact ⟨runtimeTy, current, hcell, h⟩

theorem LoopFramePost.prefix {before middle after : GIR.Frame} {frontier : ValueId}
    {scopes : List (ScopeId × ScopeInst)} (hprefix : Same frontier before middle)
    (hact : middle.act = before.act) (hdepth : middle.depth = before.depth)
    (h : LoopFramePost middle frontier scopes after) :
    LoopFramePost before frontier scopes after :=
  ⟨hprefix.trans h.values (Nat.le_refl _), h.activation.trans hact,
    h.scopesEqual, h.depth.trans hdepth⟩

theorem NextJumpPost.prefix {before middle after : GIR.Frame} {frontier counter : ValueId} {header : BlockId}
    {runtimeTy : IntTy} {current : Int} {scopes : List (ScopeId × ScopeInst)} {pt : Pt}
    (hprefix : Same frontier before middle) (hbound : counter ≤ frontier)
    (hact : middle.act = before.act) (hdepth : middle.depth = before.depth)
    (h : NextJumpPost middle header counter runtimeTy current scopes pt after) :
    NextJumpPost before header counter runtimeTy current scopes pt after :=
  ⟨h.point, (hprefix.mono hbound).trans h.values (Nat.le_refl _), h.counterValue,
    h.activation.trans hact, h.scopesEqual, h.depth.trans hdepth⟩

def StatementLoopPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (loop : Option LoopCtx) (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) ∨
  ReturnedAt cx flow pt' fr' ∨
  (∃ context, loop = some context ∧
    ((flow = .brk ∧ ExitedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr') ∨
    (flow = .cont ∧ ContinuedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr')))

def LoopCounterAt (loop : Option LoopCtx) (ls : LS) (fr : GIR.Frame) : Prop :=
  match loop with
  | none => True
  | some context => match context.cont with
    | .jump _ => True
    | .next _ _ counter => counter < ls.vals.size ∧
        ∃ runtimeTy current, fr.vals[counter]? = some (.val (.int runtimeTy current))

theorem StatementLoopPost.prefix {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls middle ls' : LS} {fr frMiddle fr' : GIR.Frame} {loop : Option LoopCtx}
    {ptMiddle pt' : Pt} {flow : Flow}
    (hrel : Rel cfg env cx fr ls) (P : Post cfg env cx ls fr middle frMiddle ptMiddle [])
    (hcounter : LoopCounterAt loop ls fr)
    (h : StatementLoopPost cfg env cx middle frMiddle ls' loop flow pt' fr') :
    StatementLoopPost cfg env cx ls fr ls' loop flow pt' fr' := by
  have hact : frMiddle.act = fr.act := P.rel.act.trans hrel.act.symm
  have hdepth : frMiddle.depth = fr.depth := P.rel.depth.trans hrel.depth.symm
  rcases h with ⟨hflow, Q⟩ | hreturned | ⟨context, hloop, htransfer⟩
  · exact Or.inl ⟨hflow, (P.comp Q).sub (by simp)⟩
  · exact Or.inr (Or.inl hreturned)
  · refine Or.inr (Or.inr ⟨context, hloop, ?_⟩)
    rcases htransfer with ⟨hflow, hpoint, hframe⟩ | ⟨hflow, hcontinue⟩
    · exact Or.inl ⟨hflow, hpoint,
        ⟨P.same.trans (hframe.values.mono P.mono) (Nat.le_refl _),
          hframe.activation.trans hact, hframe.scopesEqual, hframe.depth.trans hdepth⟩⟩
    · refine Or.inr ⟨hflow, ?_⟩
      cases hkind : context.cont with
      | jump header =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨hpoint, hframe⟩ := hcontinue
        exact ⟨hpoint, ⟨P.same.trans (hframe.values.mono P.mono) (Nat.le_refl _),
          hframe.activation.trans hact, hframe.scopesEqual, hframe.depth.trans hdepth⟩⟩
      | next header hint counter =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨runtimeTy, current, hcell, hnext⟩ := hcontinue
        have hbound : counter < ls.vals.size := by
          rw [hloop] at hcounter
          simp only [LoopCounterAt, hkind] at hcounter
          exact hcounter.1
        refine ⟨runtimeTy, current, ?_, hnext.prefix P.same (Nat.le_of_lt hbound) hact hdepth⟩
        rw [← P.same counter hbound] 
        exact hcell

theorem LoopCounterAt.afterPost {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls' : LS} {fr fr' : GIR.Frame} {loop : Option LoopCtx} {pt' : Pt}
    (h : LoopCounterAt loop ls fr) (P : Post cfg env cx ls fr ls' fr' pt' []) :
    LoopCounterAt loop ls' fr' := by
  cases loop with
  | none => trivial
  | some context =>
    cases hkind : context.cont with
    | jump header => simp [LoopCounterAt, hkind]
    | next header hint counter =>
      simp only [LoopCounterAt, hkind] at h ⊢
      obtain ⟨hbound, runtimeTy, current, hcell⟩ := h
      exact ⟨Nat.lt_of_lt_of_le hbound P.mono, runtimeTy, current,
        (P.same counter hbound).trans hcell⟩


end Goose.Lower
