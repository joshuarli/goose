import Goose.Lower.Validation.CfgUnreachableCheck
import Goose.Lower.Validation.CfgReturnWalk

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def NoReturnCode (code : List Inst) : Prop :=
  ∀ values origin, .term (.ret values origin) ∉ code

def ReturnPrefix (mayReturn : Array Bool) (code : List Inst) : Prop :=
  (∀ tail, blockReturnFlow mayReturn (code ++ tail) = .stops) ∨
  (∃ targets, ∀ tail, blockReturnFlow mayReturn (code ++ tail) = .branches targets) ∨
  (code.filterMap Inst.term? = [] ∧
    ∀ tail, blockReturnFlow mayReturn (code ++ tail) = blockReturnFlow mayReturn tail)

theorem ReturnPrefix.nil (mayReturn : Array Bool) : ReturnPrefix mayReturn [] :=
  Or.inr (Or.inr ⟨rfl, fun _ => rfl⟩)

theorem ReturnPrefix.append {mayReturn : Array Bool} {left right : List Inst}
    (one : ReturnPrefix mayReturn left) (two : ReturnPrefix mayReturn right) :
    ReturnPrefix mayReturn (left ++ right) := by
  rcases one with stops | ⟨targets, branches⟩ | ⟨terms, pass⟩
  · exact Or.inl (fun tail => by simpa only [List.append_assoc] using stops (right ++ tail))
  · exact Or.inr (Or.inl ⟨targets, fun tail => by simpa only [List.append_assoc] using branches (right ++ tail)⟩)
  · rcases two with stops | ⟨targets, branches⟩ | ⟨nextTerms, nextPass⟩
    · exact Or.inl (fun tail => by rw [List.append_assoc, pass, stops])
    · exact Or.inr (Or.inl ⟨targets, fun tail => by rw [List.append_assoc, pass, branches]⟩)
    · exact Or.inr (Or.inr ⟨by simp [List.filterMap_append, terms, nextTerms],
        fun tail => by rw [List.append_assoc, pass, nextPass]⟩)

theorem ReturnPrefix.ordinary (mayReturn : Array Bool) (inst : Inst)
    (ordinary : inst ≠ .term .unreachable) (noReturn : NoReturnCode [inst]) :
    ReturnPrefix mayReturn [inst] := by
  cases inst with
  | «def» value op =>
    cases op <;> try exact Or.inr (Or.inr ⟨rfl, fun _ => rfl⟩)
    rename_i callee args origin
    cases returns : mayReturn[callee]?.getD true with
    | false => exact Or.inl (fun tail => by simp [blockReturnFlow, returns])
    | true => exact Or.inr (Or.inr ⟨rfl, fun tail => by simp [blockReturnFlow, returns]⟩)
  | eff effect => exact Or.inr (Or.inr ⟨rfl, fun _ => rfl⟩)
  | term term =>
    cases term with
    | ret values origin => exact False.elim (noReturn values origin (by simp))
    | unreachable => exact False.elim (ordinary rfl)
    | br target args => exact Or.inr (Or.inl ⟨[target], fun _ => rfl⟩)
    | condbr condition yes yesArgs no noArgs => exact Or.inr (Or.inl ⟨[yes, no], fun _ => rfl⟩)
    | abort kind origin => exact Or.inl (fun _ => rfl)
    | exit value origin => exact Or.inl (fun _ => rfl)

theorem UnreachableCode.returnPrefix {noReturn : ContextId → Bool} {code : List Inst}
    (checked : UnreachableCode noReturn code) (noRet : NoReturnCode code)
    (mayReturn : Array Bool)
    (callees : ∀ callee, noReturn callee = true → mayReturn[callee]?.getD true = false) :
    ReturnPrefix mayReturn code := by
  induction checked with
  | nil => exact ReturnPrefix.nil mayReturn
  | @inst code prior next ordinary ih =>
    have before : NoReturnCode code := fun values origin member =>
      noRet values origin (List.mem_append_left _ member)
    have singleton : NoReturnCode [next] := fun values origin member =>
      noRet values origin (List.mem_append_right _ member)
    exact (ih before).append (ReturnPrefix.ordinary mayReturn next ordinary singleton)
  | @call code prior value callee args origin stopped ih =>
    have before : NoReturnCode code := fun values org member =>
      noRet values org (List.mem_append_left _ member)
    apply (ih before).append
    exact Or.inl (fun tail => by simp [blockReturnFlow, callees callee stopped])

theorem blockReturnFlow_branch_targets (mayReturn : Array Bool) (code : List Inst)
    (targets : List BlockId) (flow : blockReturnFlow mayReturn code = .branches targets) :
    ∀ target ∈ targets, target ∈ (code.filterMap Inst.term?).flatMap Term.successors := by
  induction code with
  | nil => cases flow
  | cons inst rest ih =>
    cases inst with
    | «def» value op =>
      cases op <;> try simpa [Inst.term?] using ih flow
      rename_i callee args origin
      simp only [blockReturnFlow] at flow
      split at flow
      · simpa [Inst.term?] using ih flow
      · cases flow
    | eff effect => simpa [Inst.term?] using ih flow
    | term term =>
      cases term <;> simp only [blockReturnFlow] at flow
      all_goals first
        | (solve | cases flow)
        | (cases flow
           intro target member
           simp [Inst.term?, Term.successors] at member ⊢
           first | (subst target; simp) | (rcases member with rfl | rfl <;> simp))

theorem FunctionUnreachable.noReturn_closed {noReturn : ContextId → Bool} {func : Func}
    (code : FunctionUnreachable noReturn func)
    (noRet : ∀ block ∈ func.blocks.toList, NoReturnCode block.insts)
    (terminators : ∀ block ∈ func.blocks.toList, block.terms ≠ [])
    (targets : ∀ block ∈ func.blocks.toList, ∀ target ∈ block.terms.flatMap Term.successors,
      target < func.blocks.size)
    (mayReturn : Array Bool)
    (callees : ∀ callee, noReturn callee = true → mayReturn[callee]?.getD true = false) :
    ReturnClosed mayReturn func (fun block => block < func.blocks.size) := by
  intro block bound
  let body := func.blocks[block]
  have row : func.blocks[block]? = some body := Array.getElem?_eq_getElem bound
  have present : body ∈ func.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)
  refine ⟨body, row, ?_⟩
  rcases (code body present).returnPrefix (noRet body present) mayReturn callees with
    stops | ⟨successors, branches⟩ | ⟨empty, _⟩
  · exact Or.inl (by simpa using stops [])
  · have flow : blockReturnFlow mayReturn body.insts = .branches successors := by simpa using branches []
    exact Or.inr ⟨successors, flow, fun target member =>
      targets body present target (blockReturnFlow_branch_targets mayReturn body.insts successors flow target member)⟩
  · exact False.elim (terminators body present empty)

theorem FunctionUnreachable.funcMayReturn_false {noReturn : ContextId → Bool} {func : Func}
    (code : FunctionUnreachable noReturn func)
    (noRet : ∀ block ∈ func.blocks.toList, NoReturnCode block.insts)
    (terminators : ∀ block ∈ func.blocks.toList, block.terms ≠ [])
    (targets : ∀ block ∈ func.blocks.toList, ∀ target ∈ block.terms.flatMap Term.successors,
      target < func.blocks.size) (nonempty : 0 < func.blocks.size)
    (mayReturn : Array Bool)
    (callees : ∀ callee, noReturn callee = true → mayReturn[callee]?.getD true = false) :
    funcMayReturn mayReturn func = false :=
  funcMayReturn_of_closed nonempty (code.noReturn_closed noRet terminators targets mayReturn callees)

end Goose.Lower.Validation
