import Goose.Lower.DemandCallReferenceComplete

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

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

theorem CallArgumentCells.next {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty} {before : LS}
    {arguments : List Arg} {index : Nat} {argument : Arg} (found : arguments[index]? = some argument)
    {values : List Val} {value : Val} {initial frame : GIR.Frame} {point : Pt}
    (previous : CallArgumentCells
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size initial)
    (post : Post cfg env cx (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
      (lowerArg argument (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerArg argument (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1, .val value)]) :
    CallArgumentCells (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1
      (values ++ [value]) (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size frame := by
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [argument] := by
    rw [List.take_add_one, found]
    simp
  rw [takeEq, lowerArgs_append_run]
  simpa [lowerArgs, bind_run, pure_run] using previous.appendPost post

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

#print axioms CallArgumentCells.next
#print axioms CallArgumentCells.appendPost
#print axioms CallArgumentCells.read
end Goose.Lower
