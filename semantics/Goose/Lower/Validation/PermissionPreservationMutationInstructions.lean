import Goose.Lower.Validation.PermissionPreservationSourceMutations
import Goose.Lower.Validation.PermissionPreservationInstructionRules
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_push_emitted_permissionInstruction
    {env : Core.TEnv} {place : Place} {expr : Expr} {origin : Option OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push place expr origin) start = .ok (type, finish))
    {results : List Ty} {before ownerState middle after : LS} {owner value result : ValueId}
    {module : GIR.Module} {func : Func}
    (ownerRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState))
    (childRun : lowerExpr expr (lowerEnv env.mod env.vars results) ownerState = (value, middle))
    (emitted : emitDef (.push owner value origin)
      (lowerEnv env.mod env.vars results) middle = (result, after))
    (live : middle.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshPermissionInstruction module func (lowerEnv env.mod env.vars results)
      before.vals.size after (.def result (.push owner value origin)) := by
  obtain ⟨info, _, _, ownerSource, writable, container⟩ := source_push_contents source
  have ownerLive := (dead_lowerExpr expr).live_before childRun live
  have evidence := lowerPlace_generated_contents place ownerSource container writable ownerRun ownerLive generated
  have ownerGenerated := generated.lowerPlace place ownerRun
  have retained := evidence.of_framed_run (loop := none) childRun (dense_lowerExpr expr)
    (advB_lowerExpr expr) (types_lowerExpr expr) (generatedTargetFrame_lowerExpr none expr)
    ownerGenerated.dense ownerGenerated.live trivial
  have middleGenerated := ownerGenerated.lowerExpr expr childRun
  have final := retained.of_framed_run (loop := none) emitted (dense_emitDef _) (advB_emitDef _)
    (types_emitDef _) (generatedTargetFrame_emitDef none _) middleGenerated.dense middleGenerated.live trivial
  exact .mutation (.push result owner value origin) final

theorem lowerExpr_pop_emitted_permissionInstruction
    {env : Core.TEnv} {place : Place} {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop place origin) start = .ok (type, finish))
    {results : List Ty} {before middle after : LS} {owner result : ValueId}
    {module : GIR.Module} {func : Func}
    (ownerRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, middle))
    (emitted : emitDef (.pop owner (some origin))
      (lowerEnv env.mod env.vars results) middle = (result, after))
    (live : middle.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshPermissionInstruction module func (lowerEnv env.mod env.vars results)
      before.vals.size after (.def result (.pop owner (some origin))) := by
  obtain ⟨info, _, _, ownerSource, writable, container⟩ := source_pop_contents source
  have evidence := lowerPlace_generated_contents place ownerSource container writable ownerRun live generated
  have middleGenerated := generated.lowerPlace place ownerRun
  have final := evidence.of_framed_run (loop := none) emitted (dense_emitDef _) (advB_emitDef _)
    (types_emitDef _) (generatedTargetFrame_emitDef none _) middleGenerated.dense middleGenerated.live trivial
  exact .mutation (.pop result owner (some origin)) final

#print axioms lowerExpr_pop_emitted_permissionInstruction

#print axioms lowerExpr_push_emitted_permissionInstruction

end Goose.Lower.Validation
