import Goose.Proofs.ConstructionStoredReadTypingPacked

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst Loc)
open Goose.Proofs.ConstructionRepresentation

theorem LayoutConforms.sequence (layout : LayoutEnv) (owner element : Ty)
    (conforms : LayoutConforms layout owner) (selected : Goose.Construct.elementType owner = some element) :
    LayoutConforms layout element := by
  cases owner <;> simp only [Goose.Construct.elementType, Option.some.injEq, reduceCtorEq] at selected
  all_goals cases selected; exact conforms

theorem readValuePath_typed (fuel : Nat) (layout : LayoutEnv) (registry : RootTypes)
    (before after : ExecutionState) (owner target : Ty) (value result : Value) (path : List Nat)
    (conforms : LayoutConforms layout owner) (represented : ValueRepresentation owner value)
    (pointers : PointerTypedValue registry owner value) (backed : ValueStorageBacked layout before value)
    (typedPath : TypePath owner path target)
    (executed : readValuePath fuel layout value path before = .ok result after) :
    after = before ∧ ValueRepresentation target result ∧ PointerTypedValue registry target result ∧
      ValueStorageBacked layout before result := by
  induction typedPath generalizing fuel value before after with
  | root ty =>
      cases fuel with
      | zero => simp only [readValuePath, timeout, EvalM.stop] at executed; cases executed
      | succ fuel =>
          simp only [readValuePath, pure] at executed
          cases executed
          exact ⟨rfl, represented, pointers, backed⟩
  | element owner element target index path sequence tail ih =>
      cases fuel with
      | zero => simp only [readValuePath, timeout, EvalM.stop] at executed; cases executed
      | succ fuel =>
          have childConforms := conforms.sequence layout owner element sequence
          cases represented with
          | integer ty number => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | boolean truth => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | unit => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | reference mutability ty location => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | slice mutability ty location start count => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | record id fields values length children => simp only [Goose.Construct.elementType, reduceCtorEq] at sequence
          | array actual count values inline length children =>
              simp only [Goose.Construct.elementType, Option.some.injEq] at sequence
              cases sequence
              have pointerChildren : ∀ item ∈ values.toList, PointerTypedValue registry element item := by
                cases pointers with | array _ _ _ children => exact children
              have backedChildren : ∀ item ∈ values.toList, ValueStorageBacked layout before item := by
                cases backed with | array _ children => exact children
              cases found : values[index]? with
              | none => simp only [readValuePath, found, bind, fault, EvalM.stop] at executed; cases executed
              | some child =>
                  simp only [readValuePath, found, bind, pure] at executed
                  have member : child ∈ values.toList := List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using found)
                  exact ih fuel before after child childConforms (children child member)
                    (pointerChildren child member) (backedChildren child member) executed
          | stored ty stored varying logical =>
              have storedBacking : StoredValueBacking layout before stored := by
                cases backed with | stored _ valid => exact valid
              have sourceElement : Goose.Construct.elementType stored.ty = some element := by rw [logical]; exact sequence
              cases step : readStoredElement fuel layout stored index before with
              | stop reason state | escape destination carriers state | jump destination kind state =>
                  simp only [readValuePath, bind, step] at executed
                  cases executed
              | ok child middle =>
                  obtain ⟨same, childRep, childPointers, childBacking⟩ :=
                    readStoredElement_typed fuel layout registry before middle stored index element child
                      storedBacking sourceElement childConforms step
                  subst middle
                  simp only [readValuePath, bind, step] at executed
                  exact ih fuel before after child childConforms childRep childPointers childBacking executed
  | field id fields index field target path selected tail ih =>
      cases fuel with
      | zero => simp only [readValuePath, timeout, EvalM.stop] at executed; cases executed
      | succ fuel =>
          have childConforms := LayoutFieldsConforms.selected layout fields conforms.2 index field selected
          cases represented with
          | stored ty stored varying logical => simp only [Ty.nonfixed, Bool.false_eq_true] at varying
          | record id types values length children =>
              have pointerChildren : ∀ (index : Nat) (ty : Ty) (item : Value), fields.toList[index]? = some ty →
                  values[index]? = some item → PointerTypedValue registry ty item := by
                cases pointers with | record _ _ _ children => exact children
              have backedChildren : ∀ item ∈ values.toList, ValueStorageBacked layout before item := by
                cases backed with | record _ _ children => exact children
              cases found : values[index]? with
              | none => simp only [readValuePath, found, bind, fault, EvalM.stop] at executed; cases executed
              | some child =>
                  simp only [readValuePath, found, bind, pure] at executed
                  have member : child ∈ values.toList := List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using found)
                  exact ih fuel before after child childConforms (children index field child selected found)
                    (pointerChildren index field child selected found) (backedChildren child member) executed

theorem readLoc_typed (fuel : Nat) (layout : LayoutEnv) (registry : RootTypes)
    (before after : ExecutionState) (liveRoots : RootInst → Prop)
    (heap : ∀ root ty item, registry root = some ty → before.objects.lookup root = some item →
      ValueRepresentation ty item ∧ PointerTypedValue registry ty item)
    (layouts : ∀ root ty, registry root = some ty → LayoutConforms layout ty)
    (backed : RootedBackingState layout before liveRoots) (location : Loc) (target : Ty) (result : Value)
    (live : liveRoots location.root) (typed : LocationTyped registry location target)
    (executed : readLoc fuel layout location before = .ok result after) :
    after = before ∧ ValueRepresentation target result ∧ PointerTypedValue registry target result ∧
      ValueStorageBacked layout before result := by
  obtain ⟨owner, registered, path⟩ := typed
  cases found : before.objects.lookup location.root with
  | none => simp only [readLoc, EvalM.get, found, bind, fault, EvalM.stop] at executed; cases executed
  | some item =>
      simp only [readLoc, EvalM.get, found, bind] at executed
      have valid := heap location.root owner item registered found
      exact readValuePath_typed fuel layout registry before after owner target item result location.path
        (layouts location.root owner registered) valid.1 valid.2
        (backed.values location.root live item found) path executed

#print axioms readValuePath_typed
#print axioms readLoc_typed

end Goose.Proofs.ConstructionAcceptedExecution
