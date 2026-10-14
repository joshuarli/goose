import Goose.Evidence.Typing

namespace Goose.Evidence

open Goose.Core Goose.GIR Goose.Proofs.Memory

theorem WeakViewTy.ofDeclaredArray {roots : RootDeclarations} {location : Loc}
    {owner element : Ty} {start len : Nat} {resizable : Bool}
    (declared : DeclaredLocation roots location owner) (arrayType : arrayElem? owner = some element) :
    WeakViewTy roots ⟨location, start, len, resizable⟩ element := by
  cases owner <;> simp only [arrayElem?] at arrayType <;> try contradiction
  case arr element count =>
    cases arrayType
    exact Or.inl ⟨count, declared⟩
  case grow element =>
    cases arrayType
    exact Or.inr (Or.inl declared)
  case growshrink element =>
    cases arrayType
    exact Or.inr (Or.inr (Or.inl declared))
  case limited element capacity =>
    cases arrayType
    exact Or.inr (Or.inr (Or.inr ⟨capacity, declared⟩))

theorem WeakViewTy.slice {roots : RootDeclarations} {view : ViewVal} {element : Ty}
    (typed : WeakViewTy roots view element) (permission : Mutability) (start len : Nat) :
    WeakValueTy roots (.slice view.loc start len) (.slice permission element) := by
  rcases typed with ⟨count, declared⟩ | declared | declared | ⟨capacity, declared⟩
  · exact Or.inr ⟨view.loc, start, len, count, rfl, declared⟩
  · exact Or.inl ⟨view.loc, start, len, .grow element, rfl, declared, rfl⟩
  · exact Or.inl ⟨view.loc, start, len, .growshrink element, rfl, declared, rfl⟩
  · exact Or.inl ⟨view.loc, start, len, .limited element capacity, rfl, declared, rfl⟩

private theorem expectInt_state {value : Val} {before after : St} {pair : IntTy × Int}
    (evaluated : expectInt value before = .ok pair after) : after = before := by
  cases value <;> simp [expectInt, pure_apply, fault, M.stop] at evaluated
  exact evaluated.2.symm

theorem evalBnd_state {fr : Frame} {len : Nat} {default : Int} {bound : Bnd}
    {before after : St} {value : Int}
    (evaluated : evalBnd fr len default bound before = .ok value after) : after = before := by
  cases bound with
  | omitted => exact (Res.ok.inj evaluated).2.symm
  | val id | fromEnd id =>
    simp only [evalBnd] at evaluated
    obtain ⟨operand, first, read, evaluated⟩ := m_bind_ok evaluated
    obtain ⟨number, second, integer, evaluated⟩ := m_bind_ok evaluated
    have firstState := (getVal_success read).2
    have secondState := expectInt_state integer
    have lastState := (Res.ok.inj evaluated).2.symm
    exact lastState.trans (secondState.trans firstState)

theorem execPure_snapshot_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {reference : ValueId} {permission resultPermission : Mutability}
    {owner element : Ty} {mode : SnapshotMode} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[reference]? = some (some (.data (.ref permission owner))))
    (arrayType : arrayElem? owner = some element)
    (evaluated : execPure cx fr (.snapshot mode reference) before = .ok cell after) :
    WeakCellTy roots cell (.view resultPermission element) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨location, rfl, declared⟩ := valueTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨array, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := readLoc_state read
  subst middle
  obtain ⟨shape, middle, shaped, evaluated⟩ := m_bind_ok evaluated
  have sameState := expectArray_state shaped
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨WeakViewTy.ofDeclaredArray declared arrayType, rfl⟩

theorem execPure_sliceView_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {sliceId : ValueId} {permission resultPermission : Mutability}
    {element : Ty} {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[sliceId]? = some (some (.data (.slice permission element))))
    (evaluated : execPure cx fr (.sliceView sliceId) before = .ok cell after) :
    WeakCellTy roots cell (.view resultPermission element) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  rcases valueTyped with ⟨location, start, len, owner, rfl, declared, ownerType⟩ |
    ⟨location, start, len, count, rfl, declared⟩
  · simp only [expectSlice, pure_bind, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    have arrayType : arrayElem? owner = some element := by
      cases owner <;> simp_all [Ty.ownerElem?, arrayElem?]
    exact ⟨WeakViewTy.ofDeclaredArray declared arrayType, rfl⟩
  · simp only [expectSlice, pure_bind, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨Or.inl ⟨count, declared⟩, rfl⟩

theorem execPure_viewSlice_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {viewId : ValueId} {permission resultPermission : Mutability}
    {element : Ty} {lo hi : Bnd} {origin : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[viewId]? = some (some (.view permission element)))
    (evaluated : execPure cx fr (.viewSlice resultPermission viewId lo hi origin) before = .ok cell after) :
    WeakCellTy roots cell (.data (.slice resultPermission element)) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨viewTyped, sameState⟩ := frameTyped.getView metadata read
  subst middle
  obtain ⟨lower, middle, lowerRead, evaluated⟩ := m_bind_ok evaluated
  have sameState := evalBnd_state lowerRead
  subst middle
  obtain ⟨upper, middle, upperRead, evaluated⟩ := m_bind_ok evaluated
  have sameState := evalBnd_state upperRead
  subst middle
  split at evaluated
  · simp only [pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨viewTyped.slice resultPermission _ _, rfl⟩
  · cases origin <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated

theorem execPure_refElem_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {viewId indexId : ValueId} {permission : Mutability}
    {element : Ty} {indexTy : IntTy} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (viewMetadata : types[viewId]? = some (some (.view permission element)))
    (indexMetadata : types[indexId]? = some (some (.data (.int indexTy))))
    (evaluated : execPure cx fr (.refElem viewId indexId) before = .ok cell after) :
    WeakCellTy roots cell (.data (.ref permission element)) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨viewTyped, sameState⟩ := frameTyped.getView viewMetadata read
  subst middle
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal indexMetadata read
  subst middle
  obtain ⟨index, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind] at evaluated
  split at evaluated
  · simp only [pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨⟨_, rfl, viewTyped.element index.toNat⟩, rfl⟩
  · simp [fault, M.stop] at evaluated

theorem execPure_indexChecked_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {viewId indexId : ValueId} {permission : Mutability}
    {element : Ty} {indexTy : IntTy} {origin : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (viewMetadata : types[viewId]? = some (some (.view permission element)))
    (indexMetadata : types[indexId]? = some (some (.data (.int indexTy))))
    (evaluated : execPure cx fr (.indexChecked viewId indexId origin) before = .ok cell after) :
    WeakCellTy roots cell (.data (.ref permission element)) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨viewTyped, sameState⟩ := frameTyped.getView viewMetadata read
  subst middle
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal indexMetadata read
  subst middle
  obtain ⟨index, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind] at evaluated
  split at evaluated
  · simp only [pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨⟨_, rfl, viewTyped.element index.toNat⟩, rfl⟩
  · cases origin <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated

end Goose.Evidence
