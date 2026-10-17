import Goose.Lower.Validation.SourceReplacementWriterLedgerInductionSyntax
import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageAll

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem source_instruction_ledger (fragment : Fragment) (env : LEnv) (before : LS) :
    EmitsOnly (InstructionSource fragment env before) before (fragment.finish env before) := by
  have ledger : ∀ node : DemandNode, ∀ fragment : Fragment,
      fragment.node = node → ∀ env before,
        EmitsOnly (InstructionSource fragment env before) before (fragment.finish env before) := by
    intro node
    apply WellFounded.induction ((measure sizeOf).wf) node
    intro node ih
    intro fragment nodeEq env before
    have neutral : ∀ instruction, ¬ WriterInstruction instruction →
        InstructionSource fragment env before instruction := by
      intro instruction nonwriter writer
      exact False.elim (nonwriter writer)
    have children : ChildrenCovered (InstructionSource fragment env before) fragment env before := by
      intro index child start row
      have actual : (fragment.children env before)[index]? = some (some (child,start)) := by
        cases found : (fragment.children env before)[index]? <;> simp_all [Fragment.child?]
      have demandRow := (fragment.children_sources env before).row actual
      have member : some child.node ∈ node.children := by
        rw [← nodeEq]
        exact List.mem_of_getElem? demandRow
      have smaller : sizeOf child.node < sizeOf node := by
        simpa [nodeEq] using demand_child_size fragment.node child.node (by simpa [nodeEq] using member)
      have smallerRelation : WellFoundedRelation.rel child.node node := by
        change sizeOf child.node < sizeOf node
        exact smaller
      have childLedger := ih child.node smallerRelation child rfl env start
      exact childLedger.map (fun instruction _ source =>
        InstructionSource.underParent row source)
    have events : EmissionsCovered (InstructionSource fragment env before) fragment env before := by
      intro emission member writer
      exact ⟨[],fragment,before,emission,SourceLoweringAt.here fragment env before,member,rfl⟩
    exact fragment_emission_coverage (InstructionSource fragment env before)
      fragment env before neutral children events
  exact ledger fragment.node fragment rfl env before

#print axioms demand_child_size
#print axioms source_instruction_ledger

end Goose.Lower.Validation.SourceReplacementWriterLedger
