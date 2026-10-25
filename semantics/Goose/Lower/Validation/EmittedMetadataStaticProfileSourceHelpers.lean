import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {profile : ArtifactProfile} {le : LEnv}

theorem EmittedProfileRun.freezeTo (mu : Mutability) (value : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.freezeTo mu value) := by
  intro before result after run checked
  rcases freezeTo_cases run with ⟨_, rfl⟩ | emitted
  · exact checked
  · exact EmittedProfileRun.emitDef (.refFreeze value) (fun _ => trivial) before result after emitted checked

theorem EmittedProfileRun.borrowTo (mu : Mutability) (value : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.borrowTo mu value) := by
  intro before result after run checked
  rcases borrowTo_cases run with frozen | borrowed
  · exact EmittedProfileRun.freezeTo mu value before result after frozen checked
  · exact EmittedProfileRun.emitDef (.ownerBorrow value) (fun _ => trivial) before result after borrowed checked

theorem EmittedProfileRun.coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    EmittedProfileRun profile le (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (EmittedProfileRun.valTy value).bind fun source => ?_
  split
  · exact EmittedProfileRun.emitDef (.refFreeze value) (fun _ => trivial)
  · exact (EmittedProfileRun.emitDef (.sliceView value) (fun _ => trivial)).bind fun view =>
      EmittedProfileRun.emitDef (.viewSlice .readOnly view .omitted .omitted (some origin)) (fun _ => trivial)
  · exact EmittedProfileRun.pure value

theorem EmittedProfileRun.coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    EmittedProfileRun profile le (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  refine EmittedProfileRun.read.bind fun env => ?_
  cases env.slots[slot]?
  · exact EmittedProfileRun.pure value
  · exact EmittedProfileRun.coerceTo _ value origin

theorem EmittedProfileRun.coerceResult (value : ValueId) (origin : OriginId) :
    EmittedProfileRun profile le (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  refine EmittedProfileRun.read.bind fun env => ?_
  cases env.results.head?
  · exact EmittedProfileRun.pure value
  · exact EmittedProfileRun.coerceTo _ value origin

theorem EmittedProfileRun.growOwner (value : ValueId) : EmittedProfileRun profile le (Goose.Lower.growOwner value) :=
  .of_blocks_eq (fun before => by
    simp only [Goose.Lower.growOwner, bind_run, valTy_run]
    cases (Goose.Lower.valTy value le before).1 with
    | view _ _ => rfl
    | data type => cases type <;> first | rfl | (rename_i mu owner; cases owner <;> rfl))

theorem EmittedProfileRun.regrowOf (owner : Option ValueId) : EmittedProfileRun profile le (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact EmittedProfileRun.pure false
  | some value => exact EmittedProfileRun.growOwner value

theorem EmittedProfileRun.eachSampled (regrow : Bool) (view : ValueId) : EmittedProfileRun profile le (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact EmittedProfileRun.emitDef (.viewLen view) (fun _ => trivial)
  · exact EmittedProfileRun.pure 0

theorem EmittedProfileRun.eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) : EmittedProfileRun profile le (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact EmittedProfileRun.pure sampled
  · exact EmittedProfileRun.emitDef (.arrayLen (owner.getD 0)) (fun _ => trivial)

theorem EmittedProfileRun.eachElemValue (slot : VarId) (byRef : Bool) (element : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.eachElemValue slot byRef element) := by
  unfold Goose.Lower.eachElemValue
  cases byRef
  · exact EmittedProfileRun.emitDef (.load element) (fun _ => trivial)
  · refine EmittedProfileRun.read.bind fun env => ?_
    cases env.vars[slot]? with
    | none => exact EmittedProfileRun.pure element
    | some localVar =>
      cases type : localVar.ty <;> simp only [type]
      all_goals first | exact EmittedProfileRun.pure element | exact EmittedProfileRun.borrowTo _ element

theorem EmittedProfileRun.loopBody (condition : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyRun : ∀ depth target, EmittedProfileRun profile le (body depth target))
    (backRun : EmittedProfileRun profile le back) : EmittedProfileRun profile le (Goose.Lower.loopBody condition body back) := by
  unfold Goose.Lower.loopBody
  exact EmittedProfileRun.get.bind fun state => (EmittedProfileRun.fork condition).bind fun pair =>
    (EmittedProfileRun.setCur _).bind fun _ => (bodyRun state.stack.length pair.2).bind fun _ =>
      backRun.bind fun _ => EmittedProfileRun.setCur _

theorem EmittedProfileRun.rangeBack (type : IntTy) (counter header : ValueId) : EmittedProfileRun profile le (Goose.Lower.rangeBack type counter header) := by
  unfold Goose.Lower.rangeBack
  refine EmittedProfileRun.isLive.bind fun live => ?_
  cases live
  · exact EmittedProfileRun.pure ()
  · exact (EmittedProfileRun.emitDef (.next type counter) (fun _ => trivial)).bind fun next =>
      EmittedProfileRun.emitTerm (.br header [next]) trivial

theorem EmittedProfileRun.lowerWhile (header : BlockId) {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionRun : EmittedProfileRun profile le condition) (bodyRun : ∀ depth target, EmittedProfileRun profile le (body depth target)) :
    EmittedProfileRun profile le (Goose.Lower.lowerWhile header condition body) := by
  unfold Goose.Lower.lowerWhile
  exact conditionRun.bind fun value => EmittedProfileRun.whenLive () _ fun _ =>
    EmittedProfileRun.loopBody value bodyRun (EmittedProfileRun.emitTerm (.br header []) trivial)

theorem EmittedProfileRun.lowerRange (type : IntTy) (counter upper header : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyRun : ∀ depth target, EmittedProfileRun profile le (body depth target)) :
    EmittedProfileRun profile le (Goose.Lower.lowerRange type counter upper header body) := by
  unfold Goose.Lower.lowerRange
  exact (EmittedProfileRun.emitDef (.cmp .lt type counter upper) (fun _ => trivial)).bind fun condition =>
    EmittedProfileRun.loopBody condition bodyRun (EmittedProfileRun.rangeBack type counter header)

theorem EmittedProfileRun.lowerEach (regrow : Bool) (owner : Option ValueId) (sampled header counter : ValueId)
    {body : Nat → BlockId → B ValueId} (bodyRun : ∀ depth target, EmittedProfileRun profile le (body depth target)) :
    EmittedProfileRun profile le (Goose.Lower.lowerEach regrow owner sampled header counter body) := by
  unfold Goose.Lower.lowerEach
  exact (EmittedProfileRun.eachLen regrow owner sampled).bind fun length =>
    (EmittedProfileRun.emitDef (.cmp .lt .i64 counter length) (fun _ => trivial)).bind fun condition =>
      EmittedProfileRun.loopBody condition bodyRun (EmittedProfileRun.rangeBack .i64 counter header)

end Goose.Lower.Validation
