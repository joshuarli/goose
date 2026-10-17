import Goose.Lower.Validation.JoinContents
import Goose.Lower.Validation.JoinContentsEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem joinLive_contents_iff {le : LEnv} {before : LS}
    {incoming : List (BlockId × ValueId)} {ty : VTy} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (typed : before.vals[(incoming.headD (0, 0)).2]? = some (some ty))
    (sources : ∀ pair ∈ incoming, pair.1 < before.blocks.size)
    (values : ∀ pair ∈ incoming, pair.2 < before.vals.size)
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized) :
    let action : B ValueId := do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    let (value, after) := action le before
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => authorized candidate ∨ candidate = value) ↔
      ∀ pair ∈ incoming, authorized pair.2 := by
  simp only [bind_run, valTy_of_recorded typed, newBlock1_run]
  let allocated : LS :=
    { before with
      blocks := before.blocks.push ⟨[(before.vals.size, ty)], #[]⟩
      vals := before.vals.push (some ty) }
  have allocation : newBlock [ty] le before = ((before.blocks.size, [before.vals.size]), allocated) :=
    newBlock1_run ty le before
  have allocatedDense := dense_newBlock [ty] le before _ allocated allocation checked bounded
  have expanded := closed.newJoin checked bounded targets nonempty allocation
  cases patched : patchBrs before.blocks.size incoming le allocated with
  | mk patchResult middle =>
      simp only [setCur_run, pure_run, List.headD_cons]
      change ContentsClosed _ _ (permissionFunc le middle) middle.vals
        (fun candidate => authorized candidate ∨ candidate = before.vals.size) ↔ _
      constructor
      · intro post pair member
        have arguments := post.patchBrs_arguments incoming allocatedDense.1 allocatedDense.2.1
          (by intro next belongs; exact Nat.lt_trans (sources next belongs) (by simp [allocated]))
          (destination := ⟨[(before.vals.size, ty)], []⟩)
          (by simp [permissionFunc, allocated, Array.getElem_push]) rfl patched (Or.inr rfl)
        rcases arguments pair member with allowed | same
        · exact allowed
        · exact (Nat.ne_of_lt (values pair member) same).elim
      · intro arguments
        exact expanded.patchBrs incoming allocatedDense.1 allocatedDense.2.1 patched
          (fun pair member => Or.inl (arguments pair member))

theorem joinValue_contents_iff {le : LEnv} {before after : LS} {endT endF : Option BlockId}
    {valueT valueF value : ValueId} {ty : VTy} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before)
    (thenBound : ∀ block, endT = some block → block < before.blocks.size)
    (elseBound : ∀ block, endF = some block → block < before.blocks.size)
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some ty))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (run : joinValue endT valueT endF valueF le before = (value, after))
    (live : after.cur.isSome = true) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => authorized candidate ∨ candidate = value) ↔
      (endT.isSome = true → authorized valueT) ∧ (endF.isSome = true → authorized valueF) := by
  have thenValueBound : endT.isSome = true → valueT < before.vals.size := by
    intro active
    exact (Array.getElem?_eq_some_iff.mp (thenTyped active)).1
  have elseValueBound : endF.isSome = true → valueF < before.vals.size := by
    intro active
    exact (Array.getElem?_eq_some_iff.mp (elseTyped active)).1
  cases endT with
  | none =>
      cases endF with
      | none =>
          simp only [joinValue, bind_run, setCur_run, pure_run] at run
          obtain ⟨_, rfl⟩ := Prod.mk.inj run
          simp at live
      | some block =>
          have result := joinLive_contents_iff (incoming := [(block, valueF)]) checked bounded targets
            (Nat.zero_lt_of_lt (elseBound block rfl)) (elseTyped rfl)
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact elseBound block rfl)
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact elseValueBound rfl) closed
          change (let (joined, final) := joinValue none valueT (some block) valueF le before
            ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le final) final.vals
              (fun candidate => authorized candidate ∨ candidate = joined) ↔
              ∀ pair ∈ [(block, valueF)], authorized pair.2) at result
          rw [run] at result
          simpa using result
  | some block =>
      cases endF with
      | none =>
          have result := joinLive_contents_iff (incoming := [(block, valueT)]) checked bounded targets
            (Nat.zero_lt_of_lt (thenBound block rfl)) (thenTyped rfl)
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact thenBound block rfl)
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact thenValueBound rfl) closed
          change (let (joined, final) := joinValue (some block) valueT none valueF le before
            ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le final) final.vals
              (fun candidate => authorized candidate ∨ candidate = joined) ↔
              ∀ pair ∈ [(block, valueT)], authorized pair.2) at result
          rw [run] at result
          simpa using result
      | some other =>
          have result := joinLive_contents_iff (incoming := [(block, valueT), (other, valueF)]) checked bounded targets
            (Nat.zero_lt_of_lt (thenBound block rfl)) (thenTyped rfl) (by
              intro pair member
              rcases List.mem_cons.mp member with rfl | member
              · exact thenBound block rfl
              · obtain rfl := List.mem_singleton.mp member; exact elseBound other rfl) (by
              intro pair member
              rcases List.mem_cons.mp member with rfl | member
              · exact thenValueBound rfl
              · obtain rfl := List.mem_singleton.mp member; exact elseValueBound rfl) closed
          change (let (joined, final) := joinValue (some block) valueT (some other) valueF le before
            ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le final) final.vals
              (fun candidate => authorized candidate ∨ candidate = joined) ↔
              ∀ pair ∈ [(block, valueT), (other, valueF)], authorized pair.2) at result
          rw [run] at result
          simpa using result

#print axioms ContentsClosed.patchBrs_arguments
#print axioms joinLive_contents_iff
#print axioms joinValue_contents_iff

end Goose.Lower.Validation
