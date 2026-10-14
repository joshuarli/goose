import Goose.Lower.WhileRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR

def TypedWhileSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (condition : Expr) (body : Core.Block) (org : OriginId) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env (.while condition body org) state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls ls' : LS) (header : BlockId) (cx : FnCtx) (fr : GIR.Frame),
    lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls') →
    ls.pp = some (header, 0) → ExtT ls' cx.fn.blocks →
    (∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) →
    Rel cfg env cx fr ls → cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx (header, 0) fr (execWhile n cfg env condition body >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls') state

theorem typedWhileSimulation_zero (cfg : Cfg) (results : List Ty)
    (condition : Expr) (body : Core.Block) (org : OriginId) :
    TypedWhileSimulation 0 cfg results condition body org := by
  intro env state source hmetadata ls ls' header cx fr hlow hpp hext hheader hrel hgir hresults
  simp only [execWhile]
  exact SimEAt.of_simG SimG.of_timeout_bind state

theorem typedStatementLoopSimulation_while {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {body : Core.Block} {org : OriginId}
    (hwhile : TypedWhileSimulation n cfg results condition body org) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.while condition body org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  apply stmt_while_loop_sim_at n loop condition body org _ ls ls' result pt cfg env cx fr state
    hlow hpp hext hrel
  intro header headerState hwhileLower hheaderPP hextHeader hheader hheaderRel
  exact hwhile env state source hmetadata headerState ls' header cx fr hwhileLower hheaderPP
    hextHeader hheader hheaderRel hgir hresults

end Goose.Lower
