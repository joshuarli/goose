import Goose.Lower.EFlow
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

end Goose.Lower
