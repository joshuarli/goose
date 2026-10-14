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

end Goose.Evidence
