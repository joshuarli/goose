import Goose.GIR.ReplacementContentFlowProofsIncomingValues

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem allIncomingValues_site {func : Func} {value source : ValueId}
    (incoming : source ∈ allIncomingValues func value) :
    ∃ block term target args receiver parameter,
      block ∈ func.blocks.toList ∧ Inst.term term ∈ block.insts ∧
      (target,args) ∈ termEdges term ∧ func.blocks[target]? = some receiver ∧
      (parameter,source) ∈ receiver.params.zip args ∧ parameter.1 = value := by
  obtain ⟨block,blockMember,incoming⟩ := List.mem_flatMap.mp incoming
  obtain ⟨inst,member,incoming⟩ := List.mem_flatMap.mp incoming
  cases inst with
  | «def» value op => simp at incoming
  | eff effect => simp at incoming
  | term term =>
      obtain ⟨pair,edgeMember,incoming⟩ := List.mem_flatMap.mp incoming
      obtain ⟨target,args⟩ := pair
      cases targetAt : func.blocks[target]? with
      | none => simp [edgeIncomingValues,targetAt] at incoming
      | some receiver =>
          simp only [edgeIncomingValues,targetAt] at incoming
          obtain ⟨actual,actualMember,mapped⟩ := List.mem_filterMap.mp incoming
          obtain ⟨parameter,argument⟩ := actual
          split at mapped
          · rename_i same
            have output := Option.some.inj mapped
            change argument = source at output
            subst argument
            exact ⟨block,term,target,args,receiver,parameter,blockMember,member,edgeMember,targetAt,actualMember,same⟩
          · cases mapped

theorem termEdges_successor {term : Term} {target : BlockId} {args : List ValueId}
    (edge : (target,args) ∈ termEdges term) : target ∈ term.successors := by
  cases term <;> simp_all [termEdges,Term.successors]
  rcases edge with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> simp

theorem termEdges_argument_used {term : Term} {target : BlockId} {args : List ValueId} {value : ValueId}
    (edge : (target,args) ∈ termEdges term) (argument : value ∈ args) : value ∈ term.uses := by
  cases term with
  | br next values =>
      have same : target = next ∧ args = values := by simpa [termEdges] using edge
      rcases same with ⟨rfl,rfl⟩
      exact argument
  | condbr condition left leftArgs right rightArgs =>
      have same : (target = left ∧ args = leftArgs) ∨ (target = right ∧ args = rightArgs) := by
        simpa [termEdges] using edge
      rcases same with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [Term.uses,argument]
  | _ => simp [termEdges] at edge

#print axioms allIncomingValues_site
#print axioms termEdges_successor
#print axioms termEdges_argument_used

end Goose.GIR.ReplacementContentFlow.Model
