import Goose.Lower.FuelBoundLeaves
import Goose.Lower.EachTypedStatement
import Goose.Lower.RangeFlow
import Goose.Lower.RangeSources

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def TypedExprFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (expression : Expr) : Prop :=
  ∀ (env : Env) (state : St) (source : ExprSource cfg env expression state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExpr expression (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalExpr n cfg env expression)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state

def TypedPlaceFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ (env : Env) (state : St) (source : PlaceSource cfg env place state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerPlace place (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalPlace n cfg env place)
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state

def TypedViewFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (view : View) : Prop :=
  ∀ (env : Env) (state : St) (source : ViewSource cfg env view state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerView view (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalView n cfg env view)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state

def TypedBoundFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (bound : Bound) : Prop :=
  ∀ (env : Env) (state : St) (source : BoundSource cfg env bound state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (bnd : Bnd) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
      (length : Nat) (default : Int),
    lowerBound bound (lowerEnv cfg.mod env.vars results) ls = (bnd,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalBound n cfg env length default bound)
      (fun value _ pt' fr' => ∃ cells, BndSpec length default bnd value cells ∧
        Post cfg env cx ls fr after fr' pt' cells) state

def TypedArgFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (arg : Arg) : Prop :=
  ∀ (env : Env) (state : St) (source : ArgSource cfg env state arg),
    source.resultsMatch results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerArg arg (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalArg n cfg env arg)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state

def TypedArgsFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (args : List Arg) : Prop :=
  ∀ (env : Env) (state : St) (sources : ∀ n, ArgsSource n cfg env args state),
    (∀ n, (sources n).resultsMatch results) →
    ∀ (ls after : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : Frame),
    lowerArgs args (lowerEnv cfg.mod env.vars results) ls = (ids,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => mapList (evalArg n cfg env) args)
      (fun values _ pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr after fr' pt' (cellsOf ids values)) state

def TypedExprsFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (expressions : List Expr) : Prop :=
  ∀ (env : Env) (state : St) (sources : ∀ n, ExprsSource n cfg env expressions state),
    (∀ n, (sources n).resultsMatch results) →
    ∀ (ls after : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : Frame),
    lowerExprs expressions (lowerEnv cfg.mod env.vars results) ls = (ids, after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => mapList (evalExpr n cfg env) expressions)
      (fun values _ pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr after fr' pt' (cellsOf ids values)) state

def TypedStatementFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (statement : Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env statement state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls after : LS) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt loop statement (lowerEnv cfg.mod env.vars results) ls = ((),after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr → GeneratedBuilderState ls → LoopBuilderFrames loop ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => execStmt n cfg env statement >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state

def TypedStatementsFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (statements : List Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtsSource cfg env statements state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls after : LS) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts loop statements (lowerEnv cfg.mod env.vars results) ls = ((),after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr → GeneratedBuilderState ls → LoopBuilderFrames loop ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => execStmts n cfg env statements >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state

def TypedBlockFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (block : Core.Block) : Prop :=
  ∀ (env : Env) (state : St) (source : BlockSource cfg env pre' block state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls after : LS) (result : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock loop pre want block (lowerEnv cfg.mod env.vars results) ls = (result,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr → GeneratedBuilderState ls → LoopBuilderFrames loop ls →
    FuelBoundAt sourceFuel fuel cx pt fr (fun n => execBlock n cfg env pre' block >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => BlockLoopPost cfg env cx ls fr after loop block want result flow pt' fr') state

def TypedWhileFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (condition : Expr) (body : Core.Block) (origin : OriginId) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env (.while condition body origin) state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls ls' : LS) (header : BlockId) (cx : FnCtx) (fr : GIR.Frame),
    lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth,exitBlock,.jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) ls = ((),ls') →
    ls.pp = some (header,0) → ExtT ls' cx.fn.blocks →
    (∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) →
    Rel cfg env cx fr ls → cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    FuelBoundAt sourceFuel fuel cx (header,0) fr (fun n => execWhile n cfg env condition body >>= prepareReturn env)
      (fun flow _ pt' fr' => StmtFlowPost cfg env cx ls fr ls' flow pt' fr') state

def TypedRangeFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (x : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId) : Prop :=
  ∀ (env : Env) (initial : St) (source : StmtSource cfg env (.forRange x lo hi body origin) initial)
    (plan : RangePlan source), SourceResults source.typingEnv source.rootsEnv results →
    ∀ (cx : FnCtx) (header output : LS) (counter bound hb : ValueId) (hint : IntTy)
      (upper : Int) (base : Frame),
    lowerRange hint counter bound hb (fun depth exit => lowerBlock
      (some ⟨depth,exit,.next hb hint counter⟩) [(x,counter,origin)] false body)
      (lowerEnv cfg.mod env.vars results) header = ((),output) →
    header.pp = some (hb,0) → ExtT output cx.fn.blocks →
    (∃ block, cx.fn.blocks[hb]? = some block ∧ block.params = [(counter,.data (.int hint))]) →
    bound < counter → counter < header.vals.size → cx.cfg.mod = lower cfg.mod →
    cx.fn.results = results → GeneratedBuilderState header →
    ∀ (current : Int) (frame : Frame) (state : St),
    RangeInv cfg env cx header counter bound plan.intTy upper base current frame →
    RangeLoopState plan state →
    FuelBoundAt sourceFuel fuel cx (hb,0) frame
      (fun n => execRange n cfg env x plan.intTy current upper body >>= prepareReturn env)
      (fun flow _ pt' fr' => RangeFlowPost cfg env cx output counter base flow pt' fr') state

def TypedEachFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty) (x : VarId)
    (idx : Option VarId) (view : View) (byRef : Bool) (block : Core.Block) (org : OriginId) : Prop :=
  ∀ (env : Env) (initial : St) (source : StmtSource cfg env (.forEach x idx view byRef block org) initial)
    (plan : EachPlan source), SourceResults source.typingEnv source.rootsEnv results →
    ∀ (cx : FnCtx) (header output : LS) (counter irView sampled hb : ValueId) (owner : Option ValueId)
      (vw : ViewVal) (base : Frame),
    lowerEach vw.resizable owner sampled hb counter (eachBodyBuilder x idx byRef block org irView counter hb)
      (lowerEnv cfg.mod env.vars results) header = ((),output) → header.pp = some (hb,0) →
    ExtT output cx.fn.blocks →
    (∃ target, cx.fn.blocks[hb]? = some target ∧ target.params = [(counter,.data (.int .i64))]) →
    counter < header.vals.size → irView < counter →
    (vw.resizable = true → owner.getD 0 < counter) → (vw.resizable = false → sampled < counter) →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState header →
    ∀ i frame state, EachInv cfg env cx header counter irView sampled owner vw base i frame →
    EachLoopState plan vw state → FuelBoundAt sourceFuel fuel cx (hb,0) frame
      (fun n => execEach n cfg env x idx byRef block vw i >>= prepareReturn env)
      (fun flow _ pt' fr' => EachFlowPost cfg env cx output counter base flow pt' fr') state

end Goose.Lower
