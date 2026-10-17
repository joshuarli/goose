import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesJoin

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem recipes_joinArms (endT endF : Option BlockId) : RecipeRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact recipes_setCur _
  all_goals
    exact RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
      RecipeRun.bind (recipes_patchBrs0 _ _) fun _ => recipes_setCur _

theorem recipes_scFork (isAnd : Bool) (value : ValueId) : RecipeRun (scFork isAnd value) := by
  unfold scFork
  refine RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact RecipeRun.bind (recipes_emitTerm _) fun _ => RecipeRun.pure _

theorem recipes_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : RecipeRun rhs) : RecipeRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact recipes_whenLive _ fun _ =>
    RecipeRun.bind (recipes_scFork _ _) fun ⟨_, _, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind typed fun _ =>
    RecipeRun.bind (recipes_emitTerm _) fun _ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.pure _

theorem recipes_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, RecipeRun (body depth exitBlock)) (hback : RecipeRun back) :
    RecipeRun (loopBody cv body back) := by
  unfold loopBody
  exact RecipeRun.bind recipes_get fun _ =>
    RecipeRun.bind (recipes_fork _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind (hbody _ _) fun _ =>
    RecipeRun.bind hback fun _ => recipes_setCur _

theorem recipes_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : RecipeRun (rangeBack t i hb) := by
  unfold rangeBack
  refine RecipeRun.bind recipes_isLive fun live => ?_
  cases live
  · exact RecipeRun.pure _
  · exact RecipeRun.bind (recipes_emitDef _) fun _ => recipes_emitTerm _


theorem recipes_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : RecipeRun cond) (hbody : ∀ d xb, RecipeRun (body d xb)) : RecipeRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact RecipeRun.bind hc fun cv => recipes_whenLive _ fun _ =>
    recipes_loopBody cv hbody (recipes_emitTerm _)

theorem recipes_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, RecipeRun (body d xb)) : RecipeRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact RecipeRun.bind (recipes_emitDef _) fun c => recipes_loopBody c hbody (recipes_rangeBack _ _ _)

theorem recipes_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, RecipeRun (body d xb)) :
    RecipeRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact RecipeRun.bind (recipes_eachLen _ _ _) fun n => RecipeRun.bind (recipes_emitDef _) fun c =>
    recipes_loopBody c hbody (recipes_rangeBack _ _ _)

theorem recipes_ifE_core (cv : ValueId) (scope : ScopeId) {a1 a2 : B ValueId} (h1 : RecipeRun a1) (h2 : RecipeRun a2) :
    RecipeRun (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      let value ← joinValue endT vt endF vf
      recordValueRootRecipe value scope
      pure value) := by
  exact recipes_whenLive _ fun _ =>
    RecipeRun.bind (recipes_fork _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind h1 fun _ =>
    RecipeRun.bind recipes_curBlock fun _ => RecipeRun.bind (recipes_setCur _) fun _ =>
    RecipeRun.bind h2 fun _ => RecipeRun.bind recipes_curBlock fun _ => recipes_joinValue_record _ _ _ _ scope

theorem recipes_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : RecipeRun a1) (h2 : RecipeRun a2) :
    RecipeRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact recipes_whenLive _ fun _ =>
    RecipeRun.bind (recipes_fork _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind h1 fun _ =>
    RecipeRun.bind recipes_curBlock fun _ => RecipeRun.bind (recipes_setCur _) fun _ =>
    RecipeRun.bind h2 fun _ => RecipeRun.bind recipes_curBlock fun _ => recipes_joinArms _ _

theorem recipes_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : RecipeRun a1) :
    RecipeRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact recipes_whenLive _ fun _ =>
    RecipeRun.bind (recipes_fork _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind h1 fun _ =>
    RecipeRun.bind (recipes_emitTerm _) fun _ => recipes_setCur _

theorem recipes_assert_core (cv : ValueId) (org : OriginId) :
    RecipeRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact recipes_whenLive _ fun _ =>
    RecipeRun.bind (recipes_fork _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_setCur _) fun _ => RecipeRun.bind (recipes_emitTerm _) fun _ => recipes_setCur _

theorem recipes_header0 {tail : BlockId → B Unit} (ht : ∀ h, RecipeRun (tail h)) :
    RecipeRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_emitTerm _) fun _ => RecipeRun.bind (recipes_setCur _) fun _ => ht _

theorem recipes_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, RecipeRun (tail h i)) :
    RecipeRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact RecipeRun.bind (recipes_newBlock _) fun ⟨_, _⟩ =>
    RecipeRun.bind (recipes_emitTerm _) fun _ => RecipeRun.bind (recipes_setCur _) fun _ => ht _ _


end Goose.Lower.Validation.SourceCanonicalRootFloors
