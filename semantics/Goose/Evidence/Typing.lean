import Goose.Evidence.MemoryTyping
import Goose.GIR.Step
import Goose.GIR.Typing

namespace Goose.Evidence

open Goose.Core Goose.GIR Goose.Proofs.Memory

def WeakViewTy (roots : RootDeclarations) (view : ViewVal) (element : Ty) : Prop :=
  (∃ count, DeclaredLocation roots view.loc (.arr element count)) ∨
  DeclaredLocation roots view.loc (.grow element) ∨
  DeclaredLocation roots view.loc (.growshrink element) ∨
  (∃ capacity, DeclaredLocation roots view.loc (.limited element capacity))

def WeakCellTy (roots : RootDeclarations) : RVal → VTy → Prop
  | .val value, .data ty => WeakValueTy roots value ty
  | .view view, .view _ element => WeakViewTy roots view element
  | _, _ => False

def WeakFrameTy (roots : RootDeclarations) (types : Array (Option VTy)) (fr : Frame) : Prop :=
  ∀ (id : ValueId) (cell : RVal) (ty : VTy), types[id]? = some (some ty) → fr.vals[id]? = some cell →
    WeakCellTy roots cell ty

theorem WeakCellTy.int {roots : RootDeclarations} {cell : RVal} {ty : IntTy}
    (typed : WeakCellTy roots cell (.data (.int ty))) :
    ∃ n, cell = .val (.int ty n) := by
  cases cell with
  | val value =>
    obtain ⟨n, rfl⟩ := WeakValueTy.int (roots := roots) typed
    exact ⟨n, rfl⟩
  | view view => exact False.elim typed

theorem WeakFrameTy.int {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {ty : IntTy} {cell : RVal}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some (.data (.int ty))))
    (present : fr.vals[id]? = some cell) :
    ∃ n, fr.vals[id]? = some (.val (.int ty n)) := by
  obtain ⟨n, same⟩ := (typed id cell _ metadata present).int
  exact ⟨n, same ▸ present⟩

theorem WeakFrameTy.set {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {cell : RVal} {ty : VTy}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some ty))
    (valueTyped : WeakCellTy roots cell ty) : WeakFrameTy roots types (fr.set id cell) := by
  intro other value otherTy otherMetadata present
  simp only [Frame.set, Std.HashMap.getElem?_insert] at present
  split at present
  · rename_i same
    have sameId : id = other := eq_of_beq same
    subst other
    cases present
    have sameTy : otherTy = ty := Option.some.inj (Option.some.inj
      (otherMetadata.symm.trans metadata))
    subst otherTy
    exact valueTyped
  · exact typed other value otherTy otherMetadata present

theorem WeakFrameTy.getVal {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {ty : Ty} {value : Val} {before after : St}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some (.data ty)))
    (read : getVal fr id before = .ok value after) :
    WeakValueTy roots value ty ∧ after = before := by
  unfold Goose.GIR.getVal getCell at read
  cases present : fr.vals[id]? with
  | none => simp [present, bind_apply, fault, M.stop] at read
  | some cell =>
    cases cell with
    | view view => simp [present, bind_apply, pure_apply, fault, M.stop] at read
    | val found =>
      simp only [present, bind_apply, pure_apply, Res.ok.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨typed id (.val found) (.data ty) metadata present, rfl⟩

theorem WeakViewTy.mono {before after : RootDeclarations} {view : ViewVal} {element : Ty}
    (extension : before.Extends after) (typed : WeakViewTy before view element) :
    WeakViewTy after view element := by
  rcases typed with ⟨count, declared⟩ | declared | declared | ⟨capacity, declared⟩
  · exact Or.inl ⟨count, declared.mono extension⟩
  · exact Or.inr (Or.inl (declared.mono extension))
  · exact Or.inr (Or.inr (Or.inl (declared.mono extension)))
  · exact Or.inr (Or.inr (Or.inr ⟨capacity, declared.mono extension⟩))

theorem WeakCellTy.mono {before after : RootDeclarations} {cell : RVal} {ty : VTy}
    (extension : before.Extends after) (typed : WeakCellTy before cell ty) :
    WeakCellTy after cell ty := by
  cases cell <;> cases ty
  · exact WeakValueTy.mono extension typed
  · exact typed
  · exact typed
  · exact WeakViewTy.mono extension typed

theorem WeakFrameTy.mono {before after : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} (extension : before.Extends after) (typed : WeakFrameTy before types fr) :
    WeakFrameTy after types fr := by
  intro id cell ty metadata present
  exact (typed id cell ty metadata present).mono extension

theorem execPure_load_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {permission : Mutability} {ty : Ty}
    {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.ref permission ty))))
    (storeTyped : WeakStoreTy roots before.store)
    (evaluated : execPure cx fr (.load id) before = .ok cell after) :
    WeakCellTy roots cell (.data ty) ∧ after = before := by
  unfold execPure at evaluated
  cases read : getVal fr id before with
  | stop outcome state => simp [bind_apply, read] at evaluated
  | ok value state =>
    obtain ⟨valueTyped, rfl⟩ := frameTyped.getVal metadata read
    obtain ⟨location, rfl, declared⟩ := valueTyped
    simp only [bind_apply, read, expectRef, pure_apply] at evaluated
    unfold readLoc at evaluated
    cases stored : state.store.read location with
    | error fault => simp [stored] at evaluated
    | ok value =>
      simp only [stored, Res.ok.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨storeTyped.read declared stored, rfl⟩

end Goose.Evidence
