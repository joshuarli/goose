import Goose.Lower.EachRuntime
import Goose.Core.Sound.Lemmas

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Memory

theorem eachLength_typed_run {vw : ViewVal} {s s' : St} {len : Nat} {element : Ty}
    (htyped : EachViewOk s.store vw element)
    (hlen : (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s') :
    s' = s ∧ SliceTy s.store vw.loc vw.start len element := by
  refine ⟨eachLength_state hlen, ?_⟩
  cases hr : vw.resizable with
  | false =>
    simp only [hr, Bool.false_eq_true, ite_false, pure_apply] at hlen
    have heq : len = vw.len := (Res.ok.inj hlen).1.symm
    rw [heq]
    exact htyped.2.1 hr
  | true =>
    simp only [hr, ite_true] at hlen
    obtain ⟨hstart, howner⟩ := htyped.2.2 hr
    rcases howner with hgrow | hgrowshrink
    all_goals
      obtain ⟨old, hread, hflat⟩ := (by assumption : LocTy s.store vw.loc _)
      cases old <;> simp only [FlatTy] at hflat
      obtain ⟨rfl, _⟩ := hflat
      simp only [lengthLoc, Store.length, hread] at hlen
      have heq := (Res.ok.inj hlen).1.symm
      rw [heq, hstart]
    · exact sliceTy_of_grow hgrow hread
    · exact sliceTy_of_growshrink hgrowshrink hread

theorem eachElement_typed_location {vw : ViewVal} {s s' : St} {len i : Nat} {element : Ty}
    (htyped : EachViewOk s.store vw element)
    (hlen : (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s')
    (hi : i < len) :
    LocTy s.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ element :=
  sliceTy_elem (eachLength_typed_run htyped hlen).2 hi

theorem eachElement_success {vw : ViewVal} {s state : St} {i : Nat} {byRef : Bool}
    {element : Ty} {value : Val}
    (hloc : LocTy s.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ element)
    (hsource : (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
      else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok value state) :
    state = s ∧ if byRef then value = .ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩
      else FlatTy element value := by
  cases byRef with
  | true =>
    simp only [ite_true, pure_apply] at hsource ⊢
    exact ⟨(Res.ok.inj hsource).2.symm, (Res.ok.inj hsource).1.symm⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, readLoc] at hsource ⊢
    obtain ⟨old, hread, hflat⟩ := hloc
    rw [hread] at hsource
    obtain ⟨rfl, hstate⟩ := Res.ok.inj hsource
    exact ⟨hstate.symm, hflat⟩

end Goose.Lower
