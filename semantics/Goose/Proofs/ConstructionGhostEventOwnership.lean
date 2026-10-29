import Goose.Proofs.ConstructionGhostInvocationEventChunks
import Goose.Proofs.ConstructionGhostStatementEvents

namespace Goose.Proofs.ConstructionGhostEventOwnership
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents

inductive EventPosition : List (List Goose.Core.ConstructionEvent) → Nat → Nat → Nat → Prop
  | here (chunk : List Goose.Core.ConstructionEvent) (rest : List (List Goose.Core.ConstructionEvent)) (index : Nat)
      (inside : index < chunk.length) : EventPosition (chunk :: rest) index 0 index
  | later (chunk : List Goose.Core.ConstructionEvent) (rest : List (List Goose.Core.ConstructionEvent))
      (index owner within : Nat) (tail : EventPosition rest index owner within) :
      EventPosition (chunk :: rest) (chunk.length + index) (owner + 1) within

theorem eventPosition_exists (chunks : List (List Goose.Core.ConstructionEvent)) (index : Nat)
    (inside : index < chunks.flatten.length) : ∃ owner within, EventPosition chunks index owner within := by
  induction chunks generalizing index with
  | nil => simp at inside
  | cons chunk rest ih =>
      simp only [List.flatten_cons, List.length_append] at inside
      by_cases first : index < chunk.length
      · exact ⟨0, index, .here chunk rest index first⟩
      · have tailInside : index - chunk.length < rest.flatten.length := by omega
        obtain ⟨owner, within, tail⟩ := ih (index - chunk.length) tailInside
        have equal : chunk.length + (index - chunk.length) = index := by omega
        rw [← equal]
        exact ⟨owner + 1, within, .later chunk rest _ owner within tail⟩

theorem eventPosition_unique_of_index {chunks : List (List Goose.Core.ConstructionEvent)}
    {firstIndex secondIndex firstOwner firstWithin secondOwner secondWithin : Nat}
    (first : EventPosition chunks firstIndex firstOwner firstWithin)
    (second : EventPosition chunks secondIndex secondOwner secondWithin) (sameIndex : firstIndex = secondIndex) :
    firstOwner = secondOwner ∧ firstWithin = secondWithin := by
  induction first generalizing secondIndex secondOwner secondWithin with
  | here chunk rest index inside =>
      cases second with
      | here => exact ⟨rfl, sameIndex⟩
      | later _ _ otherIndex owner within tail => omega
  | later chunk rest index owner within tail ih =>
      cases second with
      | here _ _ otherIndex inside => omega
      | later _ _ otherIndex otherOwner otherWithin otherTail =>
          have tailIndex : index = otherIndex := by omega
          obtain ⟨ownerEq, withinEq⟩ := ih otherTail tailIndex
          exact ⟨by simp [ownerEq], withinEq⟩

theorem eventPosition_unique {chunks : List (List Goose.Core.ConstructionEvent)} {index firstOwner firstWithin secondOwner secondWithin : Nat}
    (first : EventPosition chunks index firstOwner firstWithin) (second : EventPosition chunks index secondOwner secondWithin) :
    firstOwner = secondOwner ∧ firstWithin = secondWithin :=
  eventPosition_unique_of_index first second rfl

theorem chunksAlign_unique {visits : List (Invocation α β)} {first second : List (List Goose.Core.ConstructionEvent)}
    (left : ChunksAlign visits first) (right : ChunksAlign visits second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons visit chunk visits chunks events tail ih =>
      cases right with
      | cons _ other _ others otherEvents otherTail =>
          have equal : chunk = other := (List.append_right_inj _).mp (events.symm.trans otherEvents)
          subst other
          exact congrArg (List.cons chunk) (ih otherTail)

theorem eventPosition_value {chunks : List (List Goose.Core.ConstructionEvent)} {index owner within : Nat}
    (position : EventPosition chunks index owner within) (chunk : List Goose.Core.ConstructionEvent)
    (chunkAt : chunks[owner]? = some chunk) : chunks.flatten[index]? = chunk[within]? := by
  induction position generalizing chunk with
  | here first rest index inside =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at chunkAt
      subst chunk
      simp [List.flatten_cons, List.getElem?_append_left inside]
  | later first rest index owner within tail ih =>
      simp only [List.getElem?_cons_succ] at chunkAt
      rw [List.flatten_cons, List.getElem?_append_right (l₁ := first) (l₂ := rest.flatten)
        (i := first.length + index) (by omega)]
      simpa using ih chunk chunkAt

#print axioms eventPosition_value
theorem eventPosition_visit {visits : List (Invocation α β)} {chunks : List (List Goose.Core.ConstructionEvent)}
    {index owner within : Nat} (aligned : ChunksAlign visits chunks) (position : EventPosition chunks index owner within) :
    ∃ visit chunk, visits[owner]? = some visit ∧ chunks[owner]? = some chunk ∧ within < chunk.length ∧
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events = visit.before.construction.events ++ chunk := by
  induction position generalizing visits with
  | here chunk rest index inside =>
      cases aligned with
      | cons visit _ visits chunks events tail => exact ⟨visit, chunk, rfl, rfl, inside, events⟩
  | later chunk rest index owner within tail ih =>
      cases aligned with
      | cons visit _ visits chunks events alignedTail =>
          obtain ⟨found, sourceChunk, foundVisit, foundChunk, inside, eventEq⟩ := ih alignedTail
          exact ⟨found, sourceChunk, by simpa using foundVisit, by simpa using foundChunk, inside, eventEq⟩

#print axioms eventPosition_visit
def OwnsEvents (visits : List (Invocation α β)) (chunks : List (List Goose.Core.ConstructionEvent)) : Prop :=
  ∀ index, index < chunks.flatten.length → ∃ owner within visit chunk, EventPosition chunks index owner within ∧
    visits[owner]? = some visit ∧ chunks[owner]? = some chunk ∧ within < chunk.length ∧
    chunks.flatten[index]? = chunk[within]? ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events = visit.before.construction.events ++ chunk ∧
    ∀ otherOwner otherWithin, EventPosition chunks index otherOwner otherWithin → owner = otherOwner ∧ within = otherWithin

theorem chunksAlign_ownership {visits : List (Invocation α β)} {chunks : List (List Goose.Core.ConstructionEvent)}
    (aligned : ChunksAlign visits chunks) : OwnsEvents visits chunks := by
  intro index inside
  obtain ⟨owner, within, position⟩ := eventPosition_exists chunks index inside
  obtain ⟨visit, chunk, visitAt, chunkAt, withinBound, events⟩ := eventPosition_visit aligned position
  exact ⟨owner, within, visit, chunk, position, visitAt, chunkAt, withinBound,
    eventPosition_value position chunk chunkAt, events, fun otherOwner otherWithin other => eventPosition_unique position other⟩

theorem statementReplay_eventOwnership
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    ∃ chunks, ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ OwnsEvents (visits.map statementInvocation) chunks ∧
      ∀ otherChunks, ChunksAlign (visits.map statementInvocation) otherChunks → chunks = otherChunks := by
  obtain ⟨chunks, aligned, finalEq⟩ := invocationEvents_chunks (statementReplay_invocationEvents replay)
  exact ⟨chunks, aligned, finalEq, replay.sourceOrder, replay.once, chunksAlign_ownership aligned,
    fun other otherAligned => chunksAlign_unique aligned otherAligned⟩

#print axioms chunksAlign_ownership
#print axioms statementReplay_eventOwnership
theorem replay_eventOwnership (replay : OperandReplay action offset operands accumulator before outcome visits)
    (preserved : ∀ operand, KeepsEventPrefix (action operand)) :
    ∃ chunks : List (List Goose.Core.ConstructionEvent),
      ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      OwnsEvents visits chunks ∧
      ∀ otherChunks, ChunksAlign visits otherChunks → chunks = otherChunks := by
  obtain ⟨chunks, aligned, finalEq, ordered, once⟩ := replay_eventChunks replay preserved
  refine ⟨chunks, aligned, finalEq, ordered, once, ?_, ?_⟩
  · exact chunksAlign_ownership aligned
  · intro other otherAligned
    exact chunksAlign_unique aligned otherAligned

#print axioms eventPosition_exists
#print axioms eventPosition_unique
#print axioms chunksAlign_unique
#print axioms replay_eventOwnership
end Goose.Proofs.ConstructionGhostEventOwnership
