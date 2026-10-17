import Goose.Lower.Validation.ReplacementEmissionSite
import Goose.Lower.Validation.ReplacementEmissionMap
import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure AcceptedReplacementSite (le : LEnv) (finalState : LS)
    (owner value : ValueId) (origin : OriginId) where
  sourceEnv : Core.TEnv
  results : List Ty
  environment : lowerEnv sourceEnv.mod sourceEnv.vars results = le
  place : Place
  rhs : Expr
  scope : ScopeId
  start : Nat
  finish : Nat
  output : Core.TEnv
  accepted : Core.tyStmt sourceEnv scope (.assignWhole place rhs origin) start = .ok (output, finish)
  initial : LS
  finished : LS
  site : ReplacementEmissionSite le initial finished place rhs origin
  owner_eq : site.owner = owner
  value_eq : site.value = value
  generated : GeneratedBuilderState initial
  live : site.captured.cur.isSome = true
  extension : finished.Ext finalState
  types : TypePrefix site.addressed finalState

def AcceptedReplacementSite.retained {le : LEnv} {before after : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le before owner value origin)
    (extension : before.Ext after) (types : TypePrefix before after) :
    AcceptedReplacementSite le after owner value origin :=
  { site with extension := site.extension.trans extension, types := site.types.trans types }

theorem AcceptedReplacementSite.occurrence {le : LEnv} {finalState : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le finalState owner value origin) :
    ∃ index capturedBody finalBody tail,
      witness.site.captured.cur = some index ∧
      witness.site.captured.blocks[index]? = some capturedBody ∧
      finalState.blocks[index]? = some finalBody ∧
      finalBody.params = capturedBody.params ∧
      finalBody.insts.toList = capturedBody.insts.toList ++
        (.eff (.replace owner value (some origin)) :: tail) := by
  have addressedGenerated := witness.generated.lowerPlace witness.place witness.site.addressRun
  have clearedGenerated := addressedGenerated.emitEffect _ witness.site.clearRun
  have capturedGenerated := clearedGenerated.lowerExpr witness.rhs witness.site.rhsRun
  cases current : witness.site.captured.cur with
  | none => have active := witness.live; simp [current] at active
  | some index =>
    have bound := capturedGenerated.live index current
    let body := witness.site.captured.blocks[index]
    have row : witness.site.captured.blocks[index]? = some body := by simp [body, bound]
    have publish := witness.site.publishRun
    rw [emitEffect_run _ _ current] at publish
    have publishedRow : witness.finished.blocks[index]? =
        some { body with insts := body.insts.push (.eff (.replace owner value (some origin))) } := by
      obtain ⟨_, state⟩ := Prod.mk.inj publish
      rw [← state, Array.getElem?_modify, row]
      simp [witness.owner_eq, witness.value_eq]
    obtain ⟨finalBody, finalRow, params, tail, append⟩ := witness.extension.2 index _ publishedRow
    exact ⟨index, body, finalBody, tail, rfl, row, finalRow, params,
      by simpa [Array.toList_push, List.append_assoc] using append⟩

structure ReplacementSiteAt (le : LEnv) (state : LS) (block position : Nat)
    (owner value : ValueId) (origin : OriginId) where
  source : AcceptedReplacementSite le state owner value origin
  capturedBody : BlockB
  current : source.site.captured.cur = some block
  row : source.site.captured.blocks[block]? = some capturedBody
  position_eq : capturedBody.insts.size = position

def ReplacementSiteAt.retained {le : LEnv} {before after : LS}
    {block position owner value : Nat} {origin : OriginId}
    (site : ReplacementSiteAt le before block position owner value origin)
    (extension : before.Ext after) (types : TypePrefix before after) :
    ReplacementSiteAt le after block position owner value origin :=
  { site with source := site.source.retained extension types }

theorem ReplacementSiteAt.occurrence {le : LEnv} {state : LS}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state block position owner value origin) :
    ∃ finalBody tail, state.blocks[block]? = some finalBody ∧
      finalBody.params = witness.capturedBody.params ∧
      finalBody.insts.toList = witness.capturedBody.insts.toList ++
        (.eff (.replace owner value (some origin)) :: tail) := by
  have publish := witness.source.site.publishRun
  rw [emitEffect_run _ _ witness.current] at publish
  have publishedRow : witness.source.finished.blocks[block]? =
      some { witness.capturedBody with insts := witness.capturedBody.insts.push (.eff (.replace owner value (some origin))) } := by
    obtain ⟨_, stateEq⟩ := Prod.mk.inj publish
    rw [← stateEq, Array.getElem?_modify, witness.row]
    simp [witness.source.owner_eq, witness.source.value_eq]
  obtain ⟨finalBody, row, params, tail, append⟩ := witness.source.extension.2 block _ publishedRow
  exact ⟨finalBody, tail, row, params,
    by simpa [Array.toList_push, List.append_assoc] using append⟩

theorem AcceptedReplacementSite.captured_extension {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) :
    witness.site.captured.Ext state :=
  ((advB_emitEffect _ le witness.site.captured () witness.finished witness.site.publishRun).ext).trans witness.extension

theorem AcceptedReplacementSite.addressed_liveBound {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) : LiveBound witness.site.addressed :=
  (witness.generated.lowerPlace witness.place witness.site.addressRun).live

def ReplacementSourceAuthority (le : LEnv) (state : LS) (block position : Nat) : Inst → Prop
  | .eff (.replace owner value (some origin)) => Nonempty (ReplacementSiteAt le state block position owner value origin)
  | .eff (.replace _ _ none) => False
  | _ => True

def ReplacementSitesBuilder (le : LEnv) (state : LS) : Prop :=
  ∀ block body, state.blocks[block]? = some body → ∀ position instruction,
    body.insts[position]? = some instruction → ReplacementSourceAuthority le state block position instruction

theorem ReplacementSourceAuthority.retained {le : LEnv} {before after : LS}
    {block position : Nat} {inst : Inst}
    (valid : ReplacementSourceAuthority le before block position inst)
    (extension : before.Ext after) (types : TypePrefix before after) :
    ReplacementSourceAuthority le after block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.retained extension types⟩
  | _ => exact valid

end Goose.Lower.Validation
