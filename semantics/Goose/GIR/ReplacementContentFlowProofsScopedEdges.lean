import Goose.GIR.ReplacementContentFlowProofsScopedTyping
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.GIR.ReplacementContentFlowProofsPhi

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem edgeIncomingValues_type {func : Func} {types : Array (Option VTy)}
    {value source target : Nat} {args : List ValueId} {block : Block}
    (targetAt : func.blocks[target]? = some block)
    (typed : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      types[parameter.1]? = types[argument]?)
    (incoming : source ∈ edgeIncomingValues func value target args) :
    types[value]? = types[source]? := by
  simp only [edgeIncomingValues,targetAt] at incoming
  obtain ⟨pair,member,mapped⟩ := List.mem_filterMap.mp incoming
  split at mapped
  · rename_i same
    have result := Option.some.inj mapped
    simpa only [same,result] using typed pair.1 pair.2 member
  · cases mapped

theorem allIncomingValues_type {module : Module} {func : Func} {types : Array (Option VTy)}
    {value source : ValueId}
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      InstructionTyping module func types inst)
    (incoming : source ∈ allIncomingValues func value) : types[value]? = types[source]? := by
  obtain ⟨block,blockMember,incoming⟩ := List.mem_flatMap.mp incoming
  obtain ⟨inst,member,incoming⟩ := List.mem_flatMap.mp incoming
  cases inst with
  | «def» value op => simp at incoming
  | eff effect => simp at incoming
  | term term =>
      obtain ⟨pair,edgeMember,incoming⟩ := List.mem_flatMap.mp incoming
      have actual := typing block blockMember (.term term) member
      cases actual with
      | branch target args targetBlock targetAt typed bounded =>
          have pairAt : pair = (target,args) := by simpa [termEdges] using edgeMember
          cases pairAt
          exact edgeIncomingValues_type targetAt (fun parameter argument member => (typed parameter argument member).1) incoming
      | conditional condition left right leftArgs rightArgs leftBlock rightBlock leftAt rightAt leftTypes rightTypes leftBound rightBound =>
          have pairAt : pair = (left,leftArgs) ∨ pair = (right,rightArgs) := by simpa [termEdges] using edgeMember
          rcases pairAt with pairAt | pairAt
          · cases pairAt
            exact edgeIncomingValues_type leftAt (fun parameter argument member => (leftTypes parameter argument member).1) incoming
          · cases pairAt
            exact edgeIncomingValues_type rightAt (fun parameter argument member => (rightTypes parameter argument member).1) incoming
      | returned => simp [termEdges] at edgeMember
      | terminal term nonbranch nonconditional nonreturned =>
          cases term <;> simp [termEdges] at edgeMember
          · exact False.elim (nonbranch _ _ rfl)
          · exact False.elim (nonconditional _ _ _ _ _ rfl)

theorem allIncomingValues_absent_of_definition {func : Func} {value source : ValueId}
    {block : Block} {op : Op}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (blockMember : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts) :
    source ∉ allIncomingValues func value := by
  intro incoming
  obtain ⟨targetBlock,targetMember,incoming⟩ := List.mem_flatMap.mp incoming
  obtain ⟨inst,member,incoming⟩ := List.mem_flatMap.mp incoming
  cases inst with
  | «def» value op => simp at incoming
  | eff effect => simp at incoming
  | term term =>
      obtain ⟨pair,edgeMember,incoming⟩ := List.mem_flatMap.mp incoming
      cases targetAt : func.blocks[pair.1]? with
      | none => simp [edgeIncomingValues,targetAt] at incoming
      | some target =>
          simp only [edgeIncomingValues,targetAt] at incoming
          obtain ⟨actual,actualMember,mapped⟩ := List.mem_filterMap.mp incoming
          split at mapped
          · rename_i same
            have separate := unique_definition_not_parameter unique blockMember defined target
              (List.mem_of_getElem? (by simpa using targetAt))
            exact separate (List.mem_map.mpr ⟨actual.1,(List.of_mem_zip actualMember).1,same⟩)
          · cases mapped

#print axioms BackingOp.source_used
#print axioms edgeIncomingValues_type
#print axioms allIncomingValues_type
#print axioms allIncomingValues_absent_of_definition

end Goose.GIR.ReplacementContentFlow.Model
