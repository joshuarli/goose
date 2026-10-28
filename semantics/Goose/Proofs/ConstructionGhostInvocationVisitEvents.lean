import Goose.Proofs.ConstructionGhostInvocationEvents

namespace Goose.Proofs.ConstructionGhostInvocationVisitEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostInvocationEvents

theorem invocationEvents_prefix {before after : List Goose.Core.ConstructionEvent} {visits : List (Invocation α β)}
    (segments : InvocationEvents before visits after) : EventPrefix before after := by
  induction segments with
  | done => exact eventPrefix_refl _
  | next visit rest after segment remaining ih => exact eventPrefix_trans _ _ _ segment ih

theorem invocationEvents_visitPrefix {before after : List Goose.Core.ConstructionEvent} {visits : List (Invocation α β)}
    (segments : InvocationEvents before visits after) (visit : Invocation α β) (member : visit ∈ visits) :
    EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events after := by
  induction segments with
  | done => simp at member
  | next current rest after segment remaining ih =>
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit
        exact invocationEvents_prefix remaining
      · exact ih later

#print axioms invocationEvents_prefix
#print axioms invocationEvents_visitPrefix
end Goose.Proofs.ConstructionGhostInvocationVisitEvents
