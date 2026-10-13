import Goose.Core.Sound.ShrinkBridge
import Goose.Core.Sound.MutationPreservation
import Goose.Core.Sound.Lemmas

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

private theorem preserveProtectedType {m : Module} {G : Nat} {s s' : Store}
    {owner : RootInst} {v : Val} {T : Ty}
    (hroot : RootTyLe s s')
    (hagree : StoreLeExcept (fun r => r = owner) s s')
    (haway : T.interiorTarget?.isSome = true → ∀ r, Targets v r → r ≠ owner)
    (ht : HasTy m G s v T) : HasTy m G s' v T := by
  cases T <;> try exact ht
  case ref mu target =>
    by_cases ho : target.ownerElem?.isSome = true
    · have hex := ht
      obtain ⟨l, rfl, _⟩ := hex
      exact HasTy.owner_mono hroot ho ht
    · exact HasTy.agree hagree (haway (by simp [Ty.interiorTarget?, ho])) ht
  case slice mu element =>
    exact HasTy.agree hagree (haway rfl) ht

private theorem interiorRef {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (ht : HasTy m G s v T) (hi : T.interiorTarget?.isSome = true) : IsRef v := by
  cases T <;> simp only [Ty.interiorTarget?] at hi
  case ref mu target => obtain ⟨l, rfl, _⟩ := ht; trivial
  case slice mu element => obtain ⟨l, a, n, rfl, _⟩ := ht; trivial
  all_goals cases hi

private theorem ownerRootValue {s : Store} {o : Loc} {E : Ty} {v : Val}
    (hpath : o.path = []) (ho : LocTy s o (.growshrink E))
    (hv : s.roots[o.root]? = some v) : FlatTy (.growshrink E) v := by
  obtain ⟨w, hr, ht⟩ := ho
  obtain ⟨root, hp, hg⟩ := (read_ok_iff _ _ _).1 hr
  rw [hpath, get_nil] at hg
  cases hg
  rw [hv] at hp
  cases hp
  exact ht

private theorem nonrefTypedFlat {m : Module} {G : Nat} {s : Store} {T : Ty} {v : Val}
    (hnref : ¬ IsRef v) (hnunit : v ≠ .unit) (ht : HasTy m G s v T) :
    FlatTy T v ∧ T.isRefLike = false := by
  cases T <;> simp only [HasTy] at ht
  case ref mu target =>
    obtain ⟨l, rfl, _⟩ := ht
    exact False.elim (hnref trivial)
  case slice mu element =>
    obtain ⟨l, a, n, rfl, _⟩ := ht
    exact False.elim (hnref trivial)
  case unit => exact False.elim (hnunit ht)
  all_goals exact ⟨ht, rfl⟩

private theorem olderTarget {base : Nat} {holder target : RootInst}
    (hh : BeforeBase base holder) (ha : Older target holder) : BeforeBase base target := by
  cases holder with
  | global g =>
    cases target with
    | global g' => trivial
    | «local» a si x => exact False.elim ha
  | «local» a si x =>
    cases target with
    | global g => trivial
    | «local» a' si' x' => exact Nat.lt_of_le_of_lt ha hh

private theorem truncateObservations
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {s' : Store} {o : Loc}
    {observation : Observation} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (source : ObservedSafe m W shrinking observation s.store)
    (authority : shrinking o.root ∨ ∃ a si x, o.root = .local a si x ∧ W.base ≤ si)
    (hagree : StoreLeExcept (fun r => r = o.root) s.store s')
    (hroot : RootTyLe s.store s')
    (hownerValue : ∀ v, s.store.roots[o.root]? = some v → ¬ IsRef v ∧ v ≠ .unit) :
    PreservesRootTypes m W.G observation.roots s.store s' ∧
      PreservesValues m W.G observation.values s.store s' ∧
      ObservedSafe m W shrinking observation s' := by
  have away (r : RootInst) (hold : BeforeBase W.base r) (hp : ¬ shrinking r) : r ≠ o.root := by
    intro heq
    rcases authority with hs | ⟨a, si, x, he, hbase⟩
    · exact hp (heq ▸ hs)
    · rw [heq, he] at hold
      exact (Nat.not_lt_of_ge hbase) hold
  have rootAway : ∀ r T v, observation.roots r T → s.store.roots[r]? = some v →
      T.interiorTarget?.isSome = true → ∀ target, Targets v target → target ≠ o.root := by
    intro r T v hr hv hi target ht
    exact away target (olderTarget (source.rootsOlder r T hr) (frame.inv.age r v hv target ht))
      (source.rootsProtected r T v hr hv hi target ht)
  have valueAway : ∀ v T, observation.values v T → T.interiorTarget?.isSome = true →
      ∀ target, Targets v target → target ≠ o.root := by
    intro v T hv hi target ht
    exact away target (source.valuesOlder v T hv target ht) (source.valuesProtected v T hv hi target ht)
  have roots : PreservesRootTypes m W.G observation.roots s.store s' := by
    intro r T hr v hv ht
    by_cases he : r = o.root
    · subst r
      obtain ⟨hflat, hn⟩ := nonrefTypedFlat (hownerValue v hv).1 (hownerValue v hv).2 ht
      exact LocTy.hasTyRoot (hroot o.root T (locTy_root hv hflat)) hn
    · exact ⟨v, by rw [hagree r he]; exact hv,
        preserveProtectedType hroot hagree (rootAway r T v hr hv) ht⟩
  have values : PreservesValues m W.G observation.values s.store s' := by
    intro v T hv ht
    exact preserveProtectedType hroot hagree (valueAway v T hv) ht
  refine ⟨roots, values, source.typed.advance roots values, source.rootsOlder,
    source.valuesOlder, ?_, source.valuesProtected, source.holderTypes⟩
  intro r T v hr hv hi target ht
  obtain ⟨old, hold, htyped⟩ := source.typed.1 r T hr
  have he : r ≠ o.root := by
    intro he
    subst r
    exact (hownerValue old hold).1 (interiorRef htyped hi)
  rw [hagree r he, hold] at hv
  cases hv
  exact source.rootsProtected r T v hr hold hi target ht

/-- Shrinking an external owner uses the chosen shrink footprint. A current
local owner is younger than every inherited observation and its targets. -/
theorem Frame.truncateGrowshrinkObservations
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {s' : Store} {o : Loc} {len : Nat} {E : Ty}
    {observation : Observation} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (source : ObservedSafe m W shrinking observation s.store)
    (authority : shrinking o.root ∨ ∃ a si x, o.root = .local a si x ∧ W.base ≤ si)
    (hpath : o.path = []) (howner : LocTy s.store o (.growshrink E))
    (htruncate : s.store.truncate o len = .ok s') :
    PreservesRootTypes m W.G observation.roots s.store s' ∧
      PreservesValues m W.G observation.values s.store s' ∧
      ObservedSafe m W shrinking observation s' := by
  apply truncateObservations frame source authority
    (truncate_except_owner s.store s' o len htruncate)
    (truncate_growshrink_rootTyLe s.store s' o len E howner htruncate)
  intro v hv
  have ht := ownerRootValue hpath howner hv
  refine ⟨flat_not_ref ht, ?_⟩
  intro he
  subst v
  exact ht

/-- Limited truncation changes the owner value while retaining all locations,
so inherited observations need no exclusion from its root. -/
theorem truncateLimitedObservations
    {m : Module} {W : World} {s : St}
    {s' : Store} {o : Loc} {len capacity : Nat} {E : Ty}
    {observation : Observation} {shrinking : RootInst → Prop}
    (source : ObservedSafe m W shrinking observation s.store)
    (hpath : o.path = []) (howner : LocTy s.store o (.limited E capacity))
    (htruncate : s.store.truncate o len = .ok s') :
    PreservesRootTypes m W.G observation.roots s.store s' ∧
      PreservesValues m W.G observation.values s.store s' ∧
      ObservedSafe m W shrinking observation s' := by
  have hagree := truncate_except_owner s.store s' o len htruncate
  have hle := (truncate_limited_le s.store s' o len E capacity howner htruncate).1
  have hownerValue (v : Val) (hv : s.store.roots[o.root]? = some v) :
      ¬ IsRef v ∧ v ≠ .unit := by
    obtain ⟨w, hr, ht⟩ := howner
    obtain ⟨root, hp, hg⟩ := (read_ok_iff _ _ _).1 hr
    rw [hpath, get_nil] at hg
    cases hg
    rw [hv] at hp
    cases hp
    refine ⟨flat_not_ref ht, ?_⟩
    intro he
    subst v
    exact ht
  have roots : PreservesRootTypes m W.G observation.roots s.store s' := by
    intro r T hr v hv ht
    by_cases he : r = o.root
    · subst r
      obtain ⟨hflat, hn⟩ := nonrefTypedFlat (hownerValue v hv).1 (hownerValue v hv).2 ht
      exact LocTy.hasTyRoot (LocTy.mono hle (locTy_root hv hflat)) hn
    · exact ⟨v, by rw [hagree r he]; exact hv, HasTy.mono hle ht⟩
  have values : PreservesValues m W.G observation.values s.store s' :=
    fun _ _ _ ht => HasTy.mono hle ht
  refine ⟨roots, values, source.typed.advance roots values, source.rootsOlder,
    source.valuesOlder, ?_, source.valuesProtected, source.holderTypes⟩
  intro r T v hr hv hi target ht
  obtain ⟨old, hold, htyped⟩ := source.typed.1 r T hr
  have he : r ≠ o.root := by
    intro he
    subst r
    exact (hownerValue old hold).1 (interiorRef htyped hi)
  rw [hagree r he, hold] at hv
  cases hv
  exact source.rootsProtected r T v hr hold hi target ht

/-- Exact approval excludes retained interior targets; whole-owner references
use root typing, and limited physical runs use their declared owner type. -/
theorem shrinkApproval_retainsGrowshrinkAliases
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {s' : Store} {o : Loc} {len : Nat} {E : Ty}
    (frame : Frame m W tenv penv env s future)
    (happroval : approval.shrinkOwner.ty = some (.grow E) ∨
      approval.shrinkOwner.ty = some (.growshrink E))
    (hownerRoots : Gam env W.P approval.shrinkOwner.roots o.root)
    (hbound : ∀ g, o.root = .global g → g < W.G)
    (hpath : o.path = []) (hflat : E.flat = true)
    (howner : LocTy s.store o (.growshrink E))
    (htruncate : s.store.truncate o len = .ok s') :
    RetainsAliases m W env s.store s' approval.point.retained := by
  have hagree := truncate_except_owner s.store s' o len htruncate
  have hroot := truncate_growshrink_rootTyLe s.store s' o len E howner htruncate
  have hinvalidates : approval.shrinkOwner.invalidates = true := by
    rcases happroval with ho | ho <;> simp [DemandOwner.invalidates, ho]
  intro alias hmem
  constructor
  · intro v halias
    refine ⟨preserveProtectedType hroot hagree ?_ halias.1, halias.2⟩
    intro hi r ht
    have hd := DemandOwner.conflicts_false_disjoint hinvalidates hi (approval.safe.2 alias hmem)
    exact Ne.symm (Gam.root_ne_of_no_overlap frame hd hownerRoots (halias.2 r ht))
  · intro mu el capacity l start count hty halias hslice
    have ht : HasTy m W.G s.store (.ref l) (.ref mu (.limited el capacity)) := by
      simpa [hty] using halias.1
    obtain ⟨l', heq, hloc⟩ := ht
    cases heq
    rcases hloc with ⟨_, hl | hu, _⟩ | ⟨himpossible, _⟩
    · exact SliceTy.truncate_growshrink_limited hpath hflat howner hl htruncate hslice
    · obtain ⟨g, gl, hg, he, _⟩ := hu
      have hne : l.root ≠ o.root := by
        intro heq
        have hb := hbound g (heq.symm.trans he)
        exact Nat.not_lt_of_ge hg hb
      exact SliceTy.agree hagree hne hslice
    · simp [Ty.isSlice] at himpossible

/-- A limited truncation retains physical slots and therefore preserves every
alias without requiring conflict exclusion. -/
theorem truncateLimited_retainsAliases
    {m : Module} {W : World} {env : Env} {s s' : Store} {o : Loc}
    {len : Nat} {E : Ty} {capacity : Nat} {aliases : List RetainedAlias}
    (howner : LocTy s o (.limited E capacity))
    (htruncate : s.truncate o len = .ok s') :
    RetainsAliases m W env s s' aliases := by
  have hle := (truncate_limited_le s s' o len E capacity howner htruncate).1
  intro alias _
  constructor
  · intro v ha
    exact ⟨HasTy.mono hle ha.1, ha.2⟩
  · intro mu el cap l start count _ _ hs
    exact SliceTy.mono hle hs

end Goose.Core.Sound
