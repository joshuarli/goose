import Goose.Lower.Validation.SummaryPreservationTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem rootsOfDef_function_shape {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {before after : Func} {upper : Prov} {result : ValueId}
    (parameters : before.params = after.params)
    (contents : before.roots.contents = after.roots.contents) (op : Op) :
    rootsOfDef res vt before upper result op = rootsOfDef res vt after upper result op := by
  cases op <;> simp only [rootsOfDef, parameters, contents]

def BlockParametersAgree (before after : Func) : Prop :=
  ∀ target : BlockId, (before.blocks[target]?).map Block.params = (after.blocks[target]?).map Block.params

theorem edge_roots_closed_function_shape {before after : Func} {upper : Prov}
    {target : BlockId} {args : List ValueId}
    (parameters : BlockParametersAgree before after)
    (closed : EdgeRootsClosed before upper target args) :
    EdgeRootsClosed after upper target args := by
  intro block lookup pair member
  have same := parameters target
  cases priorLookup : before.blocks[target]? with
  | none => simp [priorLookup, lookup] at same
  | some prior =>
    simp only [priorLookup, lookup, Option.map_some, Option.some.injEq] at same
    rw [← same] at member
    exact closed prior priorLookup pair member

theorem instruction_roots_closed_function_shape {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {before after : Func} {upper : Prov} {inst : Inst}
    (parameters : before.params = after.params)
    (contents : before.roots.contents = after.roots.contents)
    (blocks : BlockParametersAgree before after)
    (closed : InstructionRootsClosed res vt before upper inst) :
    InstructionRootsClosed res vt after upper inst := by
  cases inst with
  | «def» result op =>
    change ∀ root ∈ rootsOfDef res vt after upper result op, _
    rw [← rootsOfDef_function_shape parameters contents op]
    exact closed
  | eff effect => cases effect <;> exact closed
  | term term =>
    cases term with
    | br target args => exact edge_roots_closed_function_shape blocks closed
    | condbr condition left leftArgs right rightArgs =>
      exact ⟨edge_roots_closed_function_shape blocks closed.1,
        edge_roots_closed_function_shape blocks closed.2⟩
    | _ => exact closed


theorem term_roots_closed_function_shape {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {before after : Func} {upper : Prov} {term : Term}
    (parameters : ∀ target ∈ term.successors,
      (before.blocks[target]?).map Block.params = (after.blocks[target]?).map Block.params)
    (closed : InstructionRootsClosed res vt before upper (.term term)) :
    InstructionRootsClosed res vt after upper (.term term) := by
  have edge : ∀ target args,
      (before.blocks[target]?).map Block.params = (after.blocks[target]?).map Block.params →
      EdgeRootsClosed before upper target args → EdgeRootsClosed after upper target args := by
    intro target args same prior block lookup pair member
    cases priorLookup : before.blocks[target]? with
    | none => simp [priorLookup, lookup] at same
    | some old =>
      simp only [priorLookup, lookup, Option.map_some, Option.some.injEq] at same
      rw [← same] at member
      exact prior old priorLookup pair member
  cases term with
  | br target args => exact edge target args (parameters target (by simp [Term.successors])) closed
  | condbr condition left leftArgs right rightArgs =>
    exact ⟨edge left leftArgs (parameters left (by simp [Term.successors])) closed.1,
      edge right rightArgs (parameters right (by simp [Term.successors])) closed.2⟩
  | _ => exact closed

end Goose.Lower.Validation.SummaryPreservation
