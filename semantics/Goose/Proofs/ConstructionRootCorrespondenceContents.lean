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

theorem bindRoot_localContentsCorrespondence (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (before : ExecutionState) (fuel : Nat) (layout : LayoutEnv)
    (id : VarId) (root : RootInst) (value : Value)
    (resolved : rootOf interpretation.environment id before = .ok root before)
    (rooted : LocalValueContentsRooted interpretation context id value fuel layout before)
    (separateValue : ∀ location, value = .ref location → location.root ≠ root)
    (separateVisible : ∀ other ∈ visible, ∀ actual location,
      rootOf interpretation.environment other before = .ok actual before →
      before.objects.lookup actual = some (.ref location) → location.root ≠ root)
    (previous : ContentRootCorrespondence interpretation context visible fuel layout before) :
    ∃ after, bindRoot root value before = .ok () after ∧
      ContentRootCorrespondence interpretation context (id :: visible) fuel layout after := by
  obtain ⟨after, bound, objects⟩ := bindRoot_objects root value before
  refine ⟨after, bound, ?_⟩
  intro other member roots annotated actual location loaded otherResolved found read interior reference
  have priorResolved := rootOf_transfer interpretation other after before actual otherResolved
  by_cases same : actual = root
  · subst actual
    have equalId := rootOf_variable_injective interpretation other id before root priorResolved resolved
    subst other
    have equalValue : value = .ref location := by
      simpa only [objects, List.lookup, beq_self_eq_true, Option.some.injEq] using found
    have priorRead := (bindRoot_directReference_read_iff fuel layout root value before after location loaded interior
      bound (separateValue location equalValue) reference).mpr read
    exact rooted roots annotated location equalValue loaded priorRead interior reference
  · have oldMember : other ∈ visible := by
      rcases List.mem_cons.mp member with equal | member
      · subst other
        rw [resolved] at priorResolved
        cases priorResolved
        exact (same rfl).elim
      · exact member
    have priorFound : before.objects.lookup actual = some (.ref location) := by
      rw [← bindRoot_lookup_other root actual value before after bound same]
      exact found
    have priorRead := (bindRoot_directReference_read_iff fuel layout root value before after location loaded interior
      bound (separateVisible other oldMember actual location priorResolved priorFound) reference).mpr read
    exact previous other oldMember roots annotated actual location loaded priorResolved priorFound priorRead interior reference

private def VisibleReferencesOutside (interpretation : RootInterpretation) (visible : List VarId)
    (state : ExecutionState) : Prop :=
  ∀ id ∈ visible, ∀ root location,
    rootOf interpretation.environment id state = .ok root state →
    state.objects.lookup root = some (.ref location) →
    ∀ scope variableId, location.root ≠ .local interpretation.environment.act scope variableId

private theorem bindRoot_referencesOutside (interpretation : RootInterpretation) (visible : List VarId)
    (before after : ExecutionState) (id : VarId) (root : RootInst) (value : Value)
    (bound : bindRoot root value before = .ok () after)
    (resolved : rootOf interpretation.environment id before = .ok root before)
    (outside : ∀ location, value = .ref location → ∀ scope variableId,
      location.root ≠ .local interpretation.environment.act scope variableId)
    (previous : VisibleReferencesOutside interpretation visible before) :
    VisibleReferencesOutside interpretation (id :: visible) after := by
  obtain ⟨result, evaluated, objects⟩ := bindRoot_objects root value before
  rw [bound] at evaluated
  cases evaluated
  intro other member actual location otherResolved found scope variableId
  have priorResolved := rootOf_transfer interpretation other after before actual otherResolved
  by_cases same : actual = root
  · subst actual
    have equalValue : value = .ref location := by
      simpa only [objects, List.lookup, beq_self_eq_true, Option.some.injEq] using found
    exact outside location equalValue scope variableId
  · have oldMember : other ∈ visible := by
      rcases List.mem_cons.mp member with equal | member
      · subst other
        rw [resolved] at priorResolved
        cases priorResolved
        exact (same rfl).elim
      · exact member
    have priorFound : before.objects.lookup actual = some (.ref location) := by
      rw [← bindRoot_lookup_other root actual value before after bound same]
      exact found
    exact previous other oldMember actual location priorResolved priorFound scope variableId

private theorem localValueContentsRooted_bound (interpretation : RootInterpretation) (context : Context)
    (id : VarId) (value : Value) (fuel : Nat) (layout : LayoutEnv) (before after : ExecutionState)
    (root : RootInst) (replacement : Value) (bound : bindRoot root replacement before = .ok () after)
    (outside : ∀ location, value = .ref location → location.root ≠ root)
    (valid : LocalValueContentsRooted interpretation context id value fuel layout before) :
    LocalValueContentsRooted interpretation context id value fuel layout after := by
  intro roots annotated location equal result read interior reference
  have prior := (bindRoot_directReference_read_iff fuel layout root replacement before after location result interior
    bound (outside location equal) reference).mpr read
  exact valid roots annotated location equal result prior interior reference

private theorem bindAll_contents (interpretation : RootInterpretation) (context : Context)
    (scopeInstance : Nat) (values : List (VarId × Value)) (visible : List VarId)
    (before : ExecutionState) (fuel : Nat) (layout : LayoutEnv)
    (resolved : ∀ entry ∈ values, rootOf interpretation.environment entry.1 before =
      .ok (.local interpretation.environment.act scopeInstance entry.1) before)
    (rooted : ∀ entry ∈ values, LocalValueContentsRooted interpretation context entry.1 entry.2 fuel layout before)
    (outside : ∀ entry ∈ values, ∀ location, entry.2 = .ref location → ∀ scope variableId,
      location.root ≠ .local interpretation.environment.act scope variableId)
    (previousOutside : VisibleReferencesOutside interpretation visible before)
    (previous : ContentRootCorrespondence interpretation context visible fuel layout before) :
    ∃ after, bindAll interpretation.environment.act scopeInstance values before = .ok () after ∧
      ContentRootCorrespondence interpretation context (values.map Prod.fst ++ visible) fuel layout after := by
  induction values generalizing visible before with
  | nil => exact ⟨before, rfl, previous⟩
  | cons entry rest ih =>
    have currentResolved := resolved entry (by simp)
    have currentOutside := outside entry (by simp)
    obtain ⟨middle, bound, valid⟩ := bindRoot_localContentsCorrespondence interpretation context visible before fuel layout
      entry.1 (.local interpretation.environment.act scopeInstance entry.1) entry.2 currentResolved
      (rooted entry (by simp)) (fun location equal => currentOutside location equal scopeInstance entry.1)
      (fun other member root location otherResolved found =>
        previousOutside other member root location otherResolved found scopeInstance entry.1) previous
    have advanced := bindRoot_referencesOutside interpretation visible before middle entry.1
      (.local interpretation.environment.act scopeInstance entry.1) entry.2 bound currentResolved currentOutside previousOutside
    obtain ⟨after, remaining, final⟩ := ih (entry.1 :: visible) middle
      (fun other member => rootOf_transfer interpretation other.1 before middle _ (resolved other (by simp [member])))
      (fun other member => localValueContentsRooted_bound interpretation context other.1 other.2 fuel layout before middle
        (.local interpretation.environment.act scopeInstance entry.1) entry.2 bound
        (fun location equal => outside other (by simp [member]) location equal scopeInstance entry.1)
        (rooted other (by simp [member])))
      (fun other member => outside other (by simp [member])) advanced valid
    refine ⟨after, ?_, ?_⟩
    · simpa [bindAll, List.forIn_cons, bind, pure, bound] using remaining
    · intro id member
      apply final id
      simpa only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append, or_assoc,
        or_left_comm, or_comm] using member

theorem bindAll_parameterContentsCorrespondence (caller interpretation : RootInterpretation) (context : Context)
    (scopeInstance : Nat) (values : List (VarId × Value)) (before : ExecutionState) (fuel : Nat) (layout : LayoutEnv)
    (frontier : RootFrontier caller interpretation.environment.act)
    (arguments : ∀ entry ∈ values, ∃ roots, DirectValueRooted caller roots entry.2)
    (resolved : ∀ entry ∈ values, rootOf interpretation.environment entry.1 before =
      .ok (.local interpretation.environment.act scopeInstance entry.1) before)
    (rooted : ∀ entry ∈ values, LocalValueContentsRooted interpretation context entry.1 entry.2 fuel layout before) :
    ∃ after, bindAll interpretation.environment.act scopeInstance values before = .ok () after ∧
      ContentRootCorrespondence interpretation context (values.map Prod.fst) fuel layout after := by
  simpa only [List.append_nil] using
    bindAll_contents interpretation context scopeInstance values [] before fuel layout
      resolved rooted (by
        intro entry member location equal scope variableId same
        obtain ⟨roots, rooted⟩ := arguments entry member
        have reference : DirectReference entry.2 location := by
          rw [equal]
          exact .reference location
        obtain ⟨symbolic, member, actual⟩ := rooted location reference
        rw [same] at actual
        exact Nat.lt_irrefl _ (instantiates_before frontier symbolic _ scope variableId actual))
      (by intro id absent; cases absent) (by intro id absent; cases absent)

end Goose.Proofs.ConstructionRootCorrespondence
