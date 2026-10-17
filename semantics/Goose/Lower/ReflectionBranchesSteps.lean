import Goose.Lower.ReflectionFuel

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem runAt_br1_step {cx : FnCtx} {pt : Pt} {fr : Frame} {b : BlockId} {blk : GIR.Block}
    {v p : ValueId} {ty : VTy} {x : RVal}
    (instruction : instAt cx.fn pt = some (.term (.br b [v])))
    (blockAt : cx.fn.blocks[b]? = some blk) (parameters : blk.params = [(p,ty)])
    (value : fr.vals[v]? = some x) (fuel : Nat) :
    runAt cx pt fr (fuel + 1) = runAt cx (b,0) (fr.set p x) fuel := by
  unfold runAt
  rw [instsAt_cons instruction,exec]
  simp only [mapList,getCell_of value,pure_bind,enterBlock,blockAt,parameters,
    List.length_cons,List.length_nil,↓reduceIte,bindParams,setCell_eq]
  have next : instsAt cx.fn (b,0) = blk.insts := by simp [instsAt,blockAt]
  rw [next]

theorem ReflectAtFuel.br1 {cx : FnCtx} {pt : Pt} {fr : Frame} {b : BlockId} {blk : GIR.Block}
    {v p : ValueId} {ty : VTy} {x : RVal} {fuel : Nat} {state : St}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.br b [v])))
    (blockAt : cx.fn.blocks[b]? = some blk) (parameters : blk.params = [(p,ty)])
    (value : fr.vals[v]? = some x)
    (reflection : ReflectAtFuel fuel cx (b,0) (fr.set p x) source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state :=
  ReflectAtFuel.step (congrFun (runAt_br1_step instruction blockAt parameters value fuel) state) reflection

theorem runAt_condbr_take0_step {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = []) (arguments : (if selected then targs else eargs) = [])
    (fuel : Nat) :
    runAt cx pt fr (fuel + 1) = runAt cx (if selected then tb else eb,0) fr fuel := by
  cases selected <;>
    simp only [Bool.false_eq_true,↓reduceIte] at blockAt arguments ⊢
  all_goals
    unfold runAt
    rw [instsAt_cons instruction,exec]
    simp only [getVal_of condition,Core.expectBool,pure_bind,Bool.false_eq_true,↓reduceIte,
      arguments,mapList,enterBlock,blockAt,parameters,List.length_nil,bindParams]
    simp [instsAt,blockAt]

theorem ReflectAtFuel.condbr_take0 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    {fuel : Nat} {state : St} {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = []) (arguments : (if selected then targs else eargs) = [])
    (reflection : ReflectAtFuel fuel cx (if selected then tb else eb,0) fr source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state :=
  ReflectAtFuel.step (congrFun
    (runAt_condbr_take0_step instruction condition blockAt parameters arguments fuel) state) reflection

theorem runAt_condbr_take1_step {cx : FnCtx} {pt : Pt} {fr : Frame} {c v p : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    {ty : VTy} {x : RVal}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = [(p,ty)]) (arguments : (if selected then targs else eargs) = [v])
    (value : fr.vals[v]? = some x) (fuel : Nat) :
    runAt cx pt fr (fuel + 1) = runAt cx (if selected then tb else eb,0) (fr.set p x) fuel := by
  cases selected <;>
    simp only [Bool.false_eq_true,↓reduceIte] at blockAt arguments ⊢
  all_goals
    unfold runAt
    rw [instsAt_cons instruction,exec]
    simp only [getVal_of condition,Core.expectBool,pure_bind,Bool.false_eq_true,↓reduceIte,
      arguments,mapList,getCell_of value,enterBlock,blockAt,parameters,List.length_cons,
      List.length_nil,bindParams,setCell_eq]
    simp [instsAt,blockAt]

theorem ReflectAtFuel.condbr_take1 {cx : FnCtx} {pt : Pt} {fr : Frame} {c v p : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    {ty : VTy} {x : RVal} {fuel : Nat} {state : St}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = [(p,ty)]) (arguments : (if selected then targs else eargs) = [v])
    (value : fr.vals[v]? = some x)
    (reflection : ReflectAtFuel fuel cx (if selected then tb else eb,0) (fr.set p x) source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state :=
  ReflectAtFuel.step (congrFun
    (runAt_condbr_take1_step instruction condition blockAt parameters arguments value fuel) state) reflection

end Goose.Lower
