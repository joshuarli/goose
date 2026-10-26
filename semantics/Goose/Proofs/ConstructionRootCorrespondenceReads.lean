import Goose.Proofs.ConstructionRootCorrespondenceWrites

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (Loc Stop)

private inductive ReferenceFreeValue : Value → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : ReferenceFreeValue (.int ty value)
  | boolean (value : Bool) : ReferenceFreeValue (.bool value)
  | unit : ReferenceFreeValue .unit
  | stored (value : StoredValue) : ReferenceFreeValue (.stored value)
  | array (values : Array Value) (children : ∀ child ∈ values.toList, ReferenceFreeValue child) :
      ReferenceFreeValue (.fixed values)
  | record (id : Goose.Core.StructId) (values : Array Value)
      (children : ∀ child ∈ values.toList, ReferenceFreeValue child) : ReferenceFreeValue (.record id values)

private theorem except_bind_success {α β : Type} (action : Except Stop α) (next : α → Except Stop β)
    (result : β) : (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem referenceFree_mapM {α : Type} (inputs : List α) (action : α → Except Stop Value)
    (each : ∀ input ∈ inputs, ∀ value, action input = .ok value → ReferenceFreeValue value)
    (values : List Value) (checked : inputs.mapM action = .ok values) :
    ∀ value ∈ values, ReferenceFreeValue value := by
  induction inputs generalizing values with
  | nil => cases checked; intro value absent; cases absent
  | cons head rest ih =>
    simp only [List.mapM_cons] at checked
    obtain ⟨value, first, checked⟩ := (except_bind_success _ _ _).mp checked
    obtain ⟨remaining, tail, checked⟩ := (except_bind_success _ _ _).mp checked
    cases checked
    intro selected member
    rcases List.mem_cons.mp member with equal | member
    · subst selected
      exact each head (by simp) value first
    · exact ih (fun input member => each input (by simp [member])) remaining tail selected member

private theorem fixedValue_referenceFree (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (bytes : ByteArray)
    (start : Nat) (value : Value) (checked : fixedValue fuel layout ty bytes start = .ok value) :
    ReferenceFreeValue value := by
  induction fuel generalizing ty start value with
  | zero => cases checked
  | succ fuel ih =>
    cases ty with
    | int ty =>
      simp only [fixedValue] at checked
      obtain ⟨integer, _, checked⟩ := (except_bind_success _ _ _).mp checked
      cases checked
      exact .integer _ _
    | bool =>
      cases byteAt : bytes.data[start]? <;> simp only [fixedValue, byteAt] at checked
      · cases checked
      · cases checked; exact .boolean _
    | arr element count =>
      cases width : fixedByteSize? layout element <;> simp only [fixedValue, width] at checked
      · cases checked
      · obtain ⟨values, decoded, checked⟩ := (except_bind_success _ _ _).mp checked
        cases checked
        apply ReferenceFreeValue.array
        simpa only [List.toList_toArray] using
          referenceFree_mapM (List.range count) _ (fun index _ value decoded => ih element _ value decoded) values decoded
    | structT id fields =>
      cases descriptor : layout.structs[id]? <;> simp only [fixedValue, descriptor] at checked
      · cases checked
      · obtain ⟨values, decoded, checked⟩ := (except_bind_success _ _ _).mp checked
        cases checked
        apply ReferenceFreeValue.record
        simpa only [List.toList_toArray] using
          referenceFree_mapM _ _ (fun field _ value decoded => ih field.ty _ value decoded) values decoded
    | _ => cases checked

private theorem eval_bind_success {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (result : β) :
    (action >>= next) before = .ok result after ↔
      ∃ value middle, action before = .ok value middle ∧ next value middle = .ok result after := by
  cases evaluated : action before with
  | stop reason state => simp [bind, evaluated]
  | escape target carriers state => simp [bind, evaluated]
  | jump target kind state => simp [bind, evaluated]
  | ok value middle =>
    constructor
    · intro checked
      exact ⟨value, middle, rfl, by simpa [bind, evaluated] using checked⟩
    · rintro ⟨actual, current, first, rest⟩
      cases first
      simpa [bind, evaluated] using rest

private theorem readStoredElement_referenceFree (fuel : Nat) (layout : LayoutEnv)
    (stored : StoredValue) (index : Nat) (before after : ExecutionState) (value : Value)
    (checked : readStoredElement fuel layout stored index before = .ok value after) :
    ReferenceFreeValue value := by
  unfold readStoredElement at checked
  obtain ⟨sampled, middle, _, checked⟩ := (eval_bind_success _ _ _ _ _).mp checked
  obtain ⟨bytes, run⟩ := sampled
  dsimp only at checked
  obtain ⟨interval, current, _, checked⟩ := (eval_bind_success _ _ _ _ _).mp checked
  obtain ⟨start, finish⟩ := interval
  dsimp only at checked
  split at checked
  · obtain ⟨sampled, final, _, checked⟩ := (eval_bind_success _ _ _ _ _).mp checked
    cases checked
    exact .stored _
  · cases decoded : fixedValue fuel layout run.element bytes start with
    | error reason => simp only [decoded, Goose.Construct.liftExcept] at checked; cases checked
    | ok result =>
      simp only [decoded, Goose.Construct.liftExcept, pure] at checked
      cases checked
      exact fixedValue_referenceFree fuel layout run.element bytes start _ decoded

private theorem readValuePath_referenceFree (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) (before after : ExecutionState) (result : Value)
    (free : ReferenceFreeValue value)
    (checked : readValuePath fuel layout value path before = .ok result after) :
    ReferenceFreeValue result := by
  induction fuel generalizing value path before after result with
  | zero => cases checked
  | succ fuel ih =>
    cases path with
    | nil => cases checked; exact free
    | cons index rest =>
      cases free with
      | integer ty value => cases checked
      | boolean value => cases checked
      | unit => cases checked
      | array values children =>
        cases found : values[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind] at checked; cases checked
        | some child =>
          simp only [readValuePath, found, pure, bind] at checked
          exact ih child rest before after result
            (children child (by simpa using Array.mem_of_getElem? found)) checked
      | record id values children =>
        cases found : values[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind] at checked; cases checked
        | some child =>
          simp only [readValuePath, found, pure, bind] at checked
          exact ih child rest before after result
            (children child (by simpa using Array.mem_of_getElem? found)) checked
      | stored stored =>
        simp only [readValuePath] at checked
        obtain ⟨child, middle, read, checked⟩ := (eval_bind_success _ _ _ _ _).mp checked
        exact ih child rest middle after result
          (readStoredElement_referenceFree fuel layout stored index before middle child read) checked

theorem readValuePath_directReference_transfer (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) (observed replacement : ExecutionState) (result : Value) (location : Loc)
    (checked : readValuePath fuel layout value path observed = .ok result observed)
    (reference : DirectReference result location) :
    readValuePath fuel layout value path replacement = .ok result replacement := by
  induction fuel generalizing value path observed replacement result location with
  | zero => cases checked
  | succ fuel ih =>
    cases path with
    | nil => cases checked; rfl
    | cons index rest =>
      cases value with
      | fixed values =>
        cases found : values[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind] at checked; cases checked
        | some child =>
          simp only [readValuePath, found, pure, bind] at checked ⊢
          exact ih child rest observed replacement result location checked reference
      | record id values =>
        cases found : values[index]? with
        | none => simp only [readValuePath, found, fault, EvalM.stop, bind] at checked; cases checked
        | some child =>
          simp only [readValuePath, found, pure, bind] at checked ⊢
          exact ih child rest observed replacement result location checked reference
      | stored stored =>
        have free := readValuePath_referenceFree (fuel + 1) layout (.stored stored) (index :: rest)
          observed observed result (.stored stored) checked
        cases reference <;> cases free
      | _ => cases checked

theorem readLoc_directReference_transfer (fuel : Nat) (layout : LayoutEnv) (location : Loc)
    (observed replacement : ExecutionState) (result : Value) (interior : Loc)
    (objects : replacement.objects.lookup location.root = observed.objects.lookup location.root)
    (checked : readLoc fuel layout location observed = .ok result observed)
    (reference : DirectReference result interior) :
    readLoc fuel layout location replacement = .ok result replacement := by
  cases found : observed.objects.lookup location.root with
  | none => simp only [readLoc, EvalM.get, bind, found, fault, EvalM.stop] at checked; cases checked
  | some value =>
    have read : readValuePath fuel layout value location.path observed = .ok result observed := by
      simpa only [readLoc, EvalM.get, bind, found] using checked
    have replayed := readValuePath_directReference_transfer fuel layout value location.path
      observed replacement result interior read reference
    simpa only [readLoc, EvalM.get, bind, objects, found] using replayed

theorem bindRoot_directReference_read_iff (fuel : Nat) (layout : LayoutEnv) (root : Goose.Core.RootInst)
    (value : Value) (before after : ExecutionState) (location : Loc) (result : Value) (interior : Loc)
    (bound : bindRoot root value before = .ok () after) (different : location.root ≠ root)
    (reference : DirectReference result interior) :
    readLoc fuel layout location before = .ok result before ↔
      readLoc fuel layout location after = .ok result after := by
  have same := bindRoot_lookup_other root location.root value before after bound different
  constructor
  · intro checked
    exact readLoc_directReference_transfer fuel layout location before after result interior same checked reference
  · intro checked
    exact readLoc_directReference_transfer fuel layout location after before result interior same.symm checked reference

end Goose.Proofs.ConstructionRootCorrespondence
