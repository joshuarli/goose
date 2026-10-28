import Goose.Lower.DemandCallReferenceComplete

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure CallArgumentCells (ids : List ValueId) (values : List Val) (limit : Nat) (frame : GIR.Frame) : Prop where
  length : ids.length = values.length
  bounded : ∀ id ∈ ids, id < limit
  cells : ∀ pair ∈ ids.zip values, frame.vals[pair.1]? = some (.val pair.2)

theorem CallArgumentCells.empty (limit : Nat) (frame : GIR.Frame) : CallArgumentCells [] [] limit frame := by
  exact ⟨rfl, by simp, by simp⟩

theorem CallArgumentCells.appendPost {cfg : Cfg} {env : Env} {cx : FnCtx} {before built : LS}
    {initial frame : GIR.Frame} {point : Pt} {id : ValueId} {value : Val} {ids : List ValueId} {values : List Val}
    (previous : CallArgumentCells ids values before.vals.size initial)
    (post : Post cfg env cx before initial built frame point [(id, .val value)]) :
    CallArgumentCells (ids ++ [id]) (values ++ [value]) built.vals.size frame := by
  constructor
  · simp [previous.length]
  · intro target member
    rcases List.mem_append.mp member with old | new
    · exact Nat.lt_of_lt_of_le (previous.bounded target old) post.mono
    · simp only [List.mem_singleton] at new
      subst target
      exact post.lt (id, .val value) (by simp)
  · intro pair member
    rw [List.zip_append previous.length] at member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with old | same
    · rw [post.same pair.1 (previous.bounded pair.1 ((List.of_mem_zip old).1))]
      exact previous.cells pair old
    · subst pair
      exact post.has (id, .val value) (by simp)

theorem CallArgumentCells.read {ids : List ValueId} {values : List Val} {limit : Nat} {frame : GIR.Frame}
    (cells : CallArgumentCells ids values limit frame) (state : St) :
    mapList (getVal frame) ids state = .ok values state := by
  induction ids generalizing values with
  | nil =>
    cases values with
    | nil => simp [mapList, pure_apply]
    | cons _ _ => have length := cells.length; simp at length
  | cons id rest ih =>
    cases values with
    | nil => have length := cells.length; simp at length
    | cons value values =>
      have head : frame.vals[id]? = some (.val value) := cells.cells (id, value) (by simp)
      have tail : CallArgumentCells rest values limit frame := by
        refine ⟨by simpa using cells.length, ?_, ?_⟩
        · intro other member
          exact cells.bounded other (by simp [member])
        · intro pair member
          exact cells.cells pair (by simp [member])
      have tailRead := ih tail
      simp only [mapList, bind_apply, getVal_of head, pure_apply, tailRead]

#print axioms CallArgumentCells.appendPost
#print axioms CallArgumentCells.read
end Goose.Lower
