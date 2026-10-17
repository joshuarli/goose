import Goose.Lower.Validation.PermissionPreservationInstructionRules
import Goose.Lower.Validation.PermissionPreservationArguments
import Goose.Lower.Validation.FunctionTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_call_emitted_permissionInstruction
    {env : Core.TEnv} {context : ContextId} {args : List Arg} {origin : OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (type, finish))
    {results : List Ty} {before middle after : LS} {values : List ValueId} {value : ValueId}
    {func : Func}
    (argsRun : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, middle))
    (emitted : emitDef (.call context values (some origin))
      (lowerEnv env.mod env.vars results) middle = (value, after))
    (live : middle.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshPermissionInstruction (lower env.mod) func (lowerEnv env.mod env.vars results)
      before.vals.size after (.def value (.call context values (some origin))) := by
  obtain ⟨ctx, callee, _, _, _, contextRow, calleeRow, sameLength, argsSource, _⟩ :=
    tyExpr_call_tables source
  have permitted := lowerArgs_generated_permissions args sameLength argsSource argsRun live generated
  have middleGenerated := generated.lowerArgs args argsRun
  apply FreshPermissionInstruction.call
  intro descriptor descriptorRow
  have signatures := congrArg (fun tables => tables[context]?) (lower_signatureTables env.mod)
  simp only [Array.getElem?_map, descriptorRow, Option.map_some] at signatures
  simp only [lowerEnv, Array.getElem?_map, contextRow, Option.map_some, calleeRow] at signatures
  have params : descriptor.params = callee.params.toList.map (tyOfVar callee ·.var) :=
    congrArg Prod.fst (Option.some.inj signatures)
  rw [params]
  intro entry member
  have allowed := permitted entry member
  exact allowed.mono
    (fun _ evidence => evidence.of_framed_run (loop := none) emitted (dense_emitDef _)
      (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
      middleGenerated.dense middleGenerated.live trivial)
    (fun _ evidence => evidence.of_framed_run (loop := none) emitted (dense_emitDef _)
      (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
      middleGenerated.dense middleGenerated.live trivial)

#print axioms lowerExpr_call_emitted_permissionInstruction

end Goose.Lower.Validation
