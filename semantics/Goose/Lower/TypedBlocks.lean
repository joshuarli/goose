import Goose.Lower.SourceContexts
import Goose.Lower.LoopBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

def TypedBlockLoopSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (block : Core.Block) : Prop :=
  ∀ (env : Env) (state : St) (source : BlockSource cfg env pre' block state),
    SourceResults source.typingEnv source.rootsEnv results →
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
    (ls ls' : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerBlock none pre want block (lowerEnv cfg.mod env.vars results) ls = (result, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hpre : PreRel fr pre pre') (hgir : cx.cfg.mod = lower cfg.mod)
    (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execBlock n cfg env pre' block >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' block want result) state := by
  have hs := h env state source hmetadata ls ls' result pt cx fr hlow hpp hext hrel hpre
    hgir hresults trivial trivial trivial
  rw [prepareLoopFlow_none] at hs
  exact hs.mono fun flow _ pt' fr' _ hp => BlockLoopPost.none.mp hp

end Goose.Lower
