import Goose.Proofs.ConstructionRootCorrespondenceReads
import Goose.Proofs.ConstructionRootCorrespondenceScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst VarId Loc)

def LocalValueContentsRooted (interpretation : RootInterpretation) (context : Context)
    (id : VarId) (value : Value) (fuel : Nat) (layout : LayoutEnv) (state : ExecutionState) : Prop :=
  ∀ roots, (context.contentRoots.find? (·.1 == id)).map Prod.snd = some roots →
    ∀ location, value = .ref location → ∀ result,
      readLoc fuel layout location state = .ok result state → DirectValueRooted interpretation roots result

theorem localValueContentsRooted_objects (interpretation : RootInterpretation) (context : Context)
    (id : VarId) (value : Value) (fuel : Nat) (layout : LayoutEnv) (before after : ExecutionState)
    (objects : after.objects = before.objects)
    (valid : LocalValueContentsRooted interpretation context id value fuel layout before) :
    LocalValueContentsRooted interpretation context id value fuel layout after := by
  intro roots annotated location equal result read interior reference
  have prior := readLoc_directReference_transfer fuel layout location after before result interior
    (by rw [objects]) read reference
  exact valid roots annotated location equal result prior interior reference

theorem contentRootCorrespondence_objects (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (fuel : Nat) (layout : LayoutEnv) (before after : ExecutionState)
    (objects : after.objects = before.objects)
    (valid : ContentRootCorrespondence interpretation context visible fuel layout before) :
    ContentRootCorrespondence interpretation context visible fuel layout after := by
  intro id member roots annotated root location value resolved found read interior reference
  have priorResolved := rootOf_transfer interpretation id after before root resolved
  have priorFound : before.objects.lookup root = some (.ref location) := by simpa only [objects] using found
  have priorRead := readLoc_directReference_transfer fuel layout location after before value interior
    (by rw [objects]) read reference
  exact valid id member roots annotated root location value priorResolved priorFound priorRead interior reference

private theorem content_bind_success {α β : Type} (action : Goose.Core.V α)
    (next : α → Goose.Core.V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem localCorrespondence_value_rooted (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (state : ExecutionState) (id : VarId) (root : RootInst) (value : Value)
    (annotation : List RootRef) (member : id ∈ visible)
    (resolved : rootOf interpretation.environment id state = .ok root state)
    (found : state.objects.lookup root = some value)
    (annotated : (context.varRoots.find? (·.1 == id)).map Prod.snd = some annotation)
    (valid : LocalRootCorrespondence interpretation context visible state) :
    DirectValueRooted interpretation annotation value := by
  intro location reference
  obtain ⟨actual, actualAt, rooted⟩ := valid id member root value resolved found location reference
  have equal : actual = annotation := Option.some.inj (actualAt.symm.trans annotated)
  cases equal
  exact rooted

theorem checkContent_variableContentsRooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (environment : PEnv) (context : Context) (arguments : List Arg) (argumentRoots : List (List RootRef))
    (index holder : Nat) (mutability : Goose.Core.Mutability) (root : RootInst)
    (visible : List VarId) (state : ExecutionState) (fuel : Nat) (layout : LayoutEnv)
    (argumentAt : arguments[index]? = some (.byRef mutability (.var holder)))
    (checked : checkContent environment context arguments argumentRoots index = .ok ())
    (member : holder ∈ visible)
    (resolved : rootOf caller.environment holder state = .ok root state)
    (valid : LocalRootCorrespondence caller environment.ctx visible state) :
    LocalValueContentsRooted (CallInterpretation caller callee argumentRoots) context index
      (.ref ⟨root, []⟩) fuel layout state := by
  intro contents contentAt location equal value read
  cases equal
  have nativeChecked := checked
  unfold checkContent at checked
  simp only [contentAt] at checked
  obtain ⟨mapped, _, checked⟩ := (content_bind_success _ _ _).mp checked
  cases annotationAt : environment.ann holder with
  | none => simp [argumentAt, annotationAt, Goose.Core.reject] at checked
  | some annotation =>
    cases found : state.objects.lookup root with
    | none => simp only [readLoc, EvalM.get, bind, found, fault, EvalM.stop] at read; cases read
    | some loaded =>
      cases fuel with
      | zero => simp only [readLoc, EvalM.get, bind, found, readValuePath, timeout, EvalM.stop] at read; cases read
      | succ fuel =>
        simp only [readLoc, EvalM.get, bind, found, readValuePath, pure] at read
        cases read
        exact checkContent_variableRooted caller callee environment context arguments argumentRoots index holder
          mutability contents annotation value contentAt argumentAt annotationAt nativeChecked
          (localCorrespondence_value_rooted caller environment.ctx visible state holder root value annotation
            member resolved found annotationAt valid)

theorem checkContent_referenceContentsRooted (caller : RootInterpretation) (callee : RuntimeActivation)
    (environment : PEnv) (context : Context) (arguments : List Arg) (argumentRoots : List (List RootRef))
    (index holder : Nat) (mutability : Goose.Core.Mutability) (root : RootInst) (location : Loc)
    (visible : List VarId) (state : ExecutionState) (fuel : Nat) (layout : LayoutEnv)
    (argumentAt : arguments[index]? = some (.byRef mutability (.deref (.read (.var holder)))))
    (checked : checkContent environment context arguments argumentRoots index = .ok ())
    (member : holder ∈ visible)
    (resolved : rootOf caller.environment holder state = .ok root state)
    (found : state.objects.lookup root = some (.ref location))
    (valid : ContentRootCorrespondence caller environment.ctx visible fuel layout state) :
    LocalValueContentsRooted (CallInterpretation caller callee argumentRoots) context index
      (.ref location) fuel layout state := by
  intro contents contentAt actual equal value read
  cases equal
  have nativeChecked := checked
  unfold checkContent at checked
  simp only [contentAt] at checked
  obtain ⟨mapped, _, checked⟩ := (content_bind_success _ _ _).mp checked
  cases annotationAt : environment.cont holder with
  | none => simp [argumentAt, annotationAt, Goose.Core.reject] at checked
  | some annotation =>
    exact checkContent_referenceRooted caller callee environment context arguments argumentRoots index holder
      mutability contents annotation value contentAt argumentAt annotationAt nativeChecked
      (fun interior reference => valid holder member annotation annotationAt root location value resolved found read interior reference)

end Goose.Proofs.ConstructionRootCorrespondence
