import Goose.Proofs.ExitExecutionLiveCarriers
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorLanding
import Goose.Proofs.ConstructionExecutionOwnershipSuccessorInactive

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private theorem redirected_lookup (previous : List (Nat × Nat)) (chain : List Nat) (target id : Nat) :
    (chain.map (fun key => (key, target)) ++ previous).lookup id =
      if id ∈ chain then some target else previous.lookup id := by
  induction chain with
  | nil => simp
  | cons first rest ih =>
    simp only [List.map_cons, List.cons_append, List.lookup_cons, ih, List.mem_cons]
    by_cases same : id = first
    · subst id; simp
    · have different : (id == first) = false := by simp [same]
      simp only [different, same, false_or]

private theorem successorPath_terminal_unique {state : ConstructionState} {first last other : Nat}
    (path : DestinationSuccessorPath state first last)
    (terminal : state.destinationSuccessors.lookup last = none)
    (second : DestinationSuccessorPath state first other)
    (otherTerminal : state.destinationSuccessors.lookup other = none) : last = other := by
  induction path with
  | refl =>
    cases second with
    | refl => rfl
    | next edge tail => rw [terminal] at edge; cases edge
  | next edge tail ih =>
    cases second with
    | refl => rw [otherTerminal] at edge; cases edge
    | next otherEdge otherTail =>
      have same := Option.some.inj (edge.symm.trans otherEdge)
      subst same
      exact ih terminal otherTail

private theorem successorPath_resolves {state : ConstructionState} {first last : Nat}
    (valid : DestinationSuccessorsValid state) (inside : first < state.destinations.size)
    (path : DestinationSuccessorPath state first last)
    (terminal : state.destinationSuccessors.lookup last = none) :
    destinationCurrent state first = .ok last := by
  obtain ⟨actual, resolved, _, _, actualTerminal⟩ := destinationCurrent_total state valid first inside
  have same := successorPath_terminal_unique path terminal
    (destinationCurrent_successorPath state first actual resolved) actualTerminal
  simpa only [same] using resolved

private theorem successorPath_redirect {before after : ConstructionState} (chain : List Nat) (target : Nat)
    (successors : after.destinationSuccessors = chain.map (fun key => (key, target)) ++ before.destinationSuccessors)
    {first last : Nat} (path : DestinationSuccessorPath before first last) (member : last ∈ chain) :
    DestinationSuccessorPath after first target := by
  induction path with
  | refl => exact .next (by rw [successors, redirected_lookup, ite_eq_left member]) (.refl _)
  | @next first middle last edge tail ih =>
    by_cases currentMember : first ∈ chain
    · exact .next (by rw [successors, redirected_lookup, ite_eq_left currentMember]) (.refl _)
    · exact .next (by rw [successors, redirected_lookup, ite_eq_right currentMember]; exact edge) (ih member)

theorem landingSuccessors_resolve (before after : ConstructionState) (chain : List Nat)
    (incoming receiving target : Nat)
    (valid : DestinationSuccessorsValid before)
    (size : after.destinations.size = before.destinations.size)
    (successors : after.destinationSuccessors = chain.map (fun key => (key, target)) ++ before.destinationSuccessors)
    (inside : incoming < before.destinations.size) (targetInside : target < before.destinations.size)
    (earlier : ∀ id ∈ chain, id < target)
    (resolved : destinationCurrent before incoming = .ok receiving)
    (member : receiving ∈ chain) (terminal : before.destinationSuccessors.lookup target = none) :
    destinationCurrent after incoming = .ok target := by
  have prepended := destinationSuccessorsValid_prepend before target chain valid targetInside earlier
  have afterValid : DestinationSuccessorsValid after := by
    intro id next present
    rw [successors] at present
    obtain ⟨lower, upper⟩ := prepended id next present
    exact ⟨lower, by simpa only [size] using upper⟩
  have targetOutside : target ∉ chain := by
    intro present
    have impossible := earlier target present
    omega
  apply successorPath_resolves afterValid (by simpa only [size] using inside)
  · exact successorPath_redirect chain target successors
      (destinationCurrent_successorPath before incoming receiving resolved) member
  · rw [successors, redirected_lookup, ite_eq_right targetOutside, terminal]

#print axioms landingSuccessors_resolve

end Goose.Proofs.ExitExecution
