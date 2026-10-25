import Goose.Lower.Validation.SourceValueRecipeTypesJoin

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

theorem recipeTypes_joinArms (endT endF : Option BlockId) : RecipeTypeRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact recipeTypes_setCur _
  all_goals
    exact RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
      RecipeTypeRun.bind (recipeTypes_patchBrs0 _ _) fun _ => recipeTypes_setCur _

theorem recipeTypes_scFork (isAnd : Bool) (value : ValueId) : RecipeTypeRun (scFork isAnd value) := by
  unfold scFork
  refine RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : RecipeTypeRun rhs) : RecipeTypeRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact recipeTypes_whenLive _ fun _ =>
    RecipeTypeRun.bind (recipeTypes_scFork _ _) fun ⟨_, _, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind typed fun _ =>
    RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.pure _

theorem recipeTypes_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, RecipeTypeRun (body depth exitBlock)) (hback : RecipeTypeRun back) :
    RecipeTypeRun (loopBody cv body back) := by
  unfold loopBody
  exact RecipeTypeRun.bind recipeTypes_get fun _ =>
    RecipeTypeRun.bind (recipeTypes_fork _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind (hbody _ _) fun _ =>
    RecipeTypeRun.bind hback fun _ => recipeTypes_setCur _

theorem recipeTypes_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : RecipeTypeRun (rangeBack t i hb) := by
  unfold rangeBack
  refine RecipeTypeRun.bind recipeTypes_isLive fun live => ?_
  cases live
  · exact RecipeTypeRun.pure _
  · exact RecipeTypeRun.bind (recipeTypes_emitDef _) fun _ => recipeTypes_emitTerm _


theorem recipeTypes_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : RecipeTypeRun cond) (hbody : ∀ d xb, RecipeTypeRun (body d xb)) : RecipeTypeRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact RecipeTypeRun.bind hc fun cv => recipeTypes_whenLive _ fun _ =>
    recipeTypes_loopBody cv hbody (recipeTypes_emitTerm _)

theorem recipeTypes_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, RecipeTypeRun (body d xb)) : RecipeTypeRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact RecipeTypeRun.bind (recipeTypes_emitDef _) fun c => recipeTypes_loopBody c hbody (recipeTypes_rangeBack _ _ _)

theorem recipeTypes_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, RecipeTypeRun (body d xb)) :
    RecipeTypeRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact RecipeTypeRun.bind (recipeTypes_eachLen _ _ _) fun n => RecipeTypeRun.bind (recipeTypes_emitDef _) fun c =>
    recipeTypes_loopBody c hbody (recipeTypes_rangeBack _ _ _)

theorem recipeTypes_ifE_core (cv : ValueId) (scope : ScopeId) {a1 a2 : B ValueId} (h1 : RecipeTypeRun a1) (h2 : RecipeTypeRun a2) :
    RecipeTypeRun (whenLive 0 fun _ => do
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
  exact recipeTypes_whenLive _ fun _ =>
    RecipeTypeRun.bind (recipeTypes_fork _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind h1 fun _ =>
    RecipeTypeRun.bind recipeTypes_curBlock fun _ => RecipeTypeRun.bind (recipeTypes_setCur _) fun _ =>
    RecipeTypeRun.bind h2 fun _ => RecipeTypeRun.bind recipeTypes_curBlock fun _ => recipeTypes_joinValue_record _ _ _ _ scope

theorem recipeTypes_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : RecipeTypeRun a1) (h2 : RecipeTypeRun a2) :
    RecipeTypeRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact recipeTypes_whenLive _ fun _ =>
    RecipeTypeRun.bind (recipeTypes_fork _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind h1 fun _ =>
    RecipeTypeRun.bind recipeTypes_curBlock fun _ => RecipeTypeRun.bind (recipeTypes_setCur _) fun _ =>
    RecipeTypeRun.bind h2 fun _ => RecipeTypeRun.bind recipeTypes_curBlock fun _ => recipeTypes_joinArms _ _

theorem recipeTypes_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : RecipeTypeRun a1) :
    RecipeTypeRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact recipeTypes_whenLive _ fun _ =>
    RecipeTypeRun.bind (recipeTypes_fork _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind h1 fun _ =>
    RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => recipeTypes_setCur _

theorem recipeTypes_assert_core (cv : ValueId) (org : OriginId) :
    RecipeTypeRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact recipeTypes_whenLive _ fun _ =>
    RecipeTypeRun.bind (recipeTypes_fork _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => recipeTypes_setCur _

theorem recipeTypes_header0 {tail : BlockId → B Unit} (ht : ∀ h, RecipeTypeRun (tail h)) :
    RecipeTypeRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => ht _

theorem recipeTypes_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, RecipeTypeRun (tail h i)) :
    RecipeTypeRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact RecipeTypeRun.bind (recipeTypes_newBlock _) fun ⟨_, _⟩ =>
    RecipeTypeRun.bind (recipeTypes_emitTerm _) fun _ => RecipeTypeRun.bind (recipeTypes_setCur _) fun _ => ht _ _


end Goose.Lower.Validation.SourceValueRecipeTypes
