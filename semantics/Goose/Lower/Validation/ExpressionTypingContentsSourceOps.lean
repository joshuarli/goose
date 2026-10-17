import Goose.Lower.Validation.ExpressionTypingFreshContents
import Goose.Lower.Validation.ExpressionTypingContentsOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerPlace_var_fresh_contents {env : Core.TEnv} {index : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var index) start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before) (live : before.cur = some current)
    (run : lowerPlace (.var index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, next, lookup, shape⟩ := (st_bind_ok _ _ _ _).mp source
  have row := (varOf_ok _ _ _ _).mp lookup
  have slotRow : (lowerEnv env.mod env.vars results).slots[index]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, index⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row.2.1]
  exact freshContentsEvidence_definition checked bounded live run ⟨_, slotRow⟩

theorem lowerPlace_global_fresh_contents {env : Core.TEnv} {index : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global index) start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId} {current : BlockId}
    (checked : before.DenseDefinitions) (bounded : LiveBound before) (live : before.cur = some current)
    (run : lowerPlace (.global index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  by_cases available : index < env.globalLimit
  · cases globalRow : env.mod.globals[index]? with
    | none => simp [Core.tyPlace, available, globalRow, rej_ok] at source
    | some globalVar =>
      apply freshContentsEvidence_definition checked bounded live run
      exact ⟨globalVar.kind, by simp [lowerEnv, Array.getElem?_map, globalRow]⟩
  · simp [Core.tyPlace, available, rej_ok] at source

theorem tyPlace_field_contents_children {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (writable : info.contentsWritable = true) :
    ∃ ownerInfo ownerFinish field fieldFinish,
      Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish) ∧
      Core.structField env ownerInfo.ty index ownerFinish = .ok (field, fieldFinish) ∧
      ownerInfo.contentsWritable = true ∧ field.contents = .mutable := by
  simp only [Core.tyPlace] at source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨field, fieldFinish, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  rw [shape] at writable
  have allowed := Bool.and_eq_true_iff.mp writable
  have mutable : field.contents = .mutable := by
    cases contents : field.contents <;> simp_all
  exact ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, fieldSource, allowed.1, mutable⟩

theorem lowerPlace_field_fresh_contents_of_owner {env : Core.TEnv} {owner : Place} {index : Nat}
    {info ownerInfo : PlaceInfo} {start ownerFinish finish : Nat}
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (writable : info.contentsWritable = true)
    (ownerSource : Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish))
    {results : List Ty} {before middle after : LS} {ownerValue value : ValueId}
    {mu : Mutability} {first : Nat} {current : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (ownerValue, middle))
    (ownerTyped : middle.vals[ownerValue]? = some (some (.data (.ref mu ownerInfo.ty))))
    (ownerEvidence : FreshContentsEvidence (lowerEnv env.mod env.vars results) first middle ownerValue)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerPlace (.field owner index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) first after value := by
  obtain ⟨actualInfo, actualFinish, field, fieldFinish, childSource, fieldSource, _, mutable⟩ :=
    tyPlace_field_contents_children source writable
  rw [ownerSource] at childSource
  cases Except.ok.inj childSource
  obtain ⟨id, fields, descriptor, shape, descriptorRow, _, fieldRow⟩ := structField_descriptor fieldSource
  have emitted : emitDef (.fieldAddr ownerValue index) (lowerEnv env.mod env.vars results) middle = (value, after) := by
    simpa only [lowerPlace, bind_run, ownerRun] using run
  have retained := types_emitDef (.fieldAddr ownerValue index) _ _ _ _ emitted ownerValue _ ownerTyped
  apply ownerEvidence.emitDef_dependency checked bounded live emitted
  intro authorized permitted
  exact ⟨permitted, mu, id, fields, descriptor, field,
    by simpa only [shape] using retained, descriptorRow, fieldRow, mutable⟩

#print axioms lowerPlace_field_fresh_contents_of_owner

end Goose.Lower.Validation
