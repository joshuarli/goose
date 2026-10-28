import Goose.Proofs.ConstructionGhostInvocationEvents

namespace Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostInvocationEvents Goose.Proofs.ConstructionExecution

inductive ChunksAlign : List (Invocation α β) → List (List Goose.Core.ConstructionEvent) → Prop
  | nil : ChunksAlign [] []
  | cons (visit : Invocation α β) (chunk : List Goose.Core.ConstructionEvent) (visits : List (Invocation α β))
      (chunks : List (List Goose.Core.ConstructionEvent))
      (events : (Goose.Proofs.Exit.stepState visit.outcome).construction.events = visit.before.construction.events ++ chunk)
      (tail : ChunksAlign visits chunks) : ChunksAlign (visit :: visits) (chunk :: chunks)

theorem invocationEvents_chunks (segments : InvocationEvents before visits after) :
    ∃ chunks : List (List Goose.Core.ConstructionEvent),
      ChunksAlign visits chunks ∧
      after = before ++ chunks.flatten := by
  induction segments with
  | done events => exact ⟨[], .nil, by simp⟩
  | next visit rest after segment remaining ih =>
      obtain ⟨chunk, chunkEq⟩ := segment
      obtain ⟨chunks, aligned, finalEq⟩ := ih
      refine ⟨chunk :: chunks, .cons visit chunk rest chunks chunkEq aligned, ?_⟩
      simp only [List.flatten_cons]
      rw [finalEq, chunkEq, List.append_assoc]

theorem replay_eventChunks (replay : OperandReplay action offset operands accumulator before outcome visits)
    (preserved : ∀ operand, KeepsEventPrefix (action operand)) :
    ∃ chunks : List (List Goose.Core.ConstructionEvent),
      ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup := by
  obtain ⟨chunks, aligned, finalEq⟩ := invocationEvents_chunks (replay_invocationEvents replay preserved)
  exact ⟨chunks, aligned, finalEq, replay.sourceOrder, replay.once⟩

#print axioms invocationEvents_chunks
#print axioms replay_eventChunks
end Goose.Proofs.ConstructionGhostInvocationEventChunks
