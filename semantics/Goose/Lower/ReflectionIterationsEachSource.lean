import Goose.Lower.ReflectionIterationsEachEffects
import Goose.Lower.ReflectionPlaces
import Goose.Lower.EachStatic

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem leaf_def_keep_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls middle after : LS}
    {fr before : Frame} {pt : Pt} {cells : List (ValueId × RVal)} {fuel sourceFuel : Nat} {state : St}
    (post : Post cfg env cx ls fr middle before pt cells) {op : Op} {le : LEnv} {id : ValueId}
    (emit : emitDef op le middle = (id,after)) (extension : ExtT after cx.fn.blocks)
    (noncall : ∀ f args org, op ≠ .call f args org) {source : Nat → M α} (inject : α → RVal)
    (equal : execPure cx before op = source sourceFuel >>= fun value => pure (inject value)) :
    ReflectAtFuel fuel cx pt before source
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' ((id,inject value) :: cells)) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
  | succ fuel =>
    have instruction := (Post.def_leaf_keep post emit extension (.val .unit)).2
    have operation : ∀ n, execOp n cx before op = execPure cx before op := by
      intro n
      cases op with
      | call f args org => exact (noncall f args org rfl).elim
      | _ => unfold execOp; rfl
    have reflected : ReflectMFuel fuel (fun n => source n >>= fun value => pure (inject value))
        (fun n => execOp n cx before op) state := ReflectMFuel.of_eq (by rw [operation,equal])
    refine (ReflectAtFuel.def_step inject instruction reflected).mono ?_
    rintro value after pt' fr' ⟨rfl,rfl⟩
    exact (Post.def_leaf_keep post emit extension (inject value)).1

def EachSourceChildReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) : View → Prop
  | .of place => TypedPlaceReflection fuel cfg results place
  | .val expr => TypedExprReflection fuel cfg results expr

theorem EachPlan.sourceReflection {fuel : Nat} {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (results : List Ty)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (childReflection : EachSourceChildReflection fuel cfg results view)
    (cx : FnCtx) (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (input output : LS) (frame : Frame) (point : Pt) (owner : Option ValueId) (irView : ValueId)
    (lowering : lowerEachSource view (lowerEnv cfg.mod env.vars results) input = ((owner,irView),output))
    (atPoint : input.pp = some point) (extension : ExtT output cx.fn.blocks)
    (related : Rel cfg env cx frame input) (generated : GeneratedBuilderState input) :
    ReflectAtFuel fuel cx point frame (fun n => evalView n cfg env view)
      (fun value _ pt' fr' => Post cfg env cx input frame output fr' pt' (EachSourceCells owner irView value)) initial := by
  have viewMetadata : SourceResults plan.viewSource.typingEnv plan.viewSource.rootsEnv results := by
    rw [plan.viewTyping,plan.viewRoots]; exact metadata
  cases view with
  | of place =>
    obtain ⟨child,typing,roots, _⟩ := plan.viewSource.ofChild
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      rw [typing,roots]; exact viewMetadata
    simp only [lowerEachSource,bind_eq] at lowering
    obtain ⟨address,middle,placeRun,snapshotId,withView,snapshotRun,resultRun⟩ := lowering
    rw [pure_run] at resultRun
    obtain ⟨pair,rfl⟩ := Prod.mk.inj resultRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
    have middleExtension := extension.of_adv (adv_emitDef snapshotRun)
    have first := childReflection env initial child childMetadata input middle address point cx frame placeRun
      atPoint middleExtension related moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx point frame
        (fun n => evalPlace n cfg env place >>= fun loc => (readLoc loc >>= expectArray) >>=
          fun pair => pure (⟨loc,0,pair.1,pair.2⟩ : ViewVal))
        (fun value _ pt' fr' => Post cfg env cx input frame withView fr' pt'
          (EachSourceCells (some address) snapshotId value)) initial := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n loc after pt' fr' done post residual bound
      have cell := post.has (address,.val (.ref loc)) (by simp)
      have equal : execPure cx fr' (.snapshot (match place with | .var _ | .global _ => .owner | _ => .borrowed) address) =
          (readLoc loc >>= expectArray) >>= fun pair => pure (.view ⟨loc,0,pair.1,pair.2⟩) := by
        simp [execPure,getVal_of cell,expectRef]
      have reflected := leaf_def_keep_reflectAtFuel (fuel := residual) (state := after) post snapshotRun extension
        (by simp) (source := fun _ => readLoc loc >>= expectArray) (sourceFuel := 0)
        (fun pair => .view ⟨loc,0,pair.1,pair.2⟩) equal
      refine reflected.bind ?_ (fun _ _ _ => MonoM.refl _) (fun _ _ _ _ => MonoM.refl _)
      intro n pair after pt' fr' done post residual bound
      exact ReflectAtFuel.ret residual (by simpa [EachSourceCells] using post)
    exact composition.of_source (fun n => ⟨n + 1,by simp only [evalView,bind_assoc]⟩)
  | val expr =>
    obtain ⟨child,typing,roots,mutability,type⟩ := plan.viewSource.valChild
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      rw [typing,roots]; exact viewMetadata
    simp only [lowerEachSource,bind_eq] at lowering
    obtain ⟨id,middle,expressionRun,snapshotId,withView,snapshotRun,resultRun⟩ := lowering
    rw [pure_run] at resultRun
    obtain ⟨pair,rfl⟩ := Prod.mk.inj resultRun
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
    have middleExtension := extension.of_adv (adv_emitDef snapshotRun)
    have first := childReflection env initial child childMetadata input middle id point cx frame expressionRun
      atPoint middleExtension related moduleEq resultsEq generated
    have composition : ReflectAtFuel fuel cx point frame
        (fun n => evalExpr n cfg env expr >>= fun value => expectSlice value >>= fun slice =>
          pure (⟨slice.1,slice.2.1,slice.2.2,false⟩ : ViewVal))
        (fun value _ pt' fr' => Post cfg env cx input frame withView fr' pt'
          (EachSourceCells none snapshotId value)) initial := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
        (fun _ _ _ _ => MonoM.refl _)
      intro n value after pt' fr' done post residual bound
      have typed := (child.result n value done).typed
      rw [type] at typed
      obtain ⟨loc,start,len,rfl,_⟩ := typed
      simp only [expectSlice,pure_bind]
      have cell := post.has (id,.val (.slice loc start len)) (by simp)
      have reflected := leaf_def_reflectAtFuel (fuel := residual) (state := after) post snapshotRun extension
        (by simp) (source := fun _ => pure ()) (sourceFuel := 0)
        (fun _ => RVal.view ⟨loc,start,len,false⟩) (by simp [execPure,getVal_of cell,expectSlice])
      have boundReflection : ReflectAtFuel residual cx pt' fr'
          (fun _ => (pure () : M Unit) >>= fun _ => pure (⟨loc,start,len,false⟩ : ViewVal))
          (fun value _ pt' fr' => Post cfg env cx input frame withView fr' pt'
            (EachSourceCells none snapshotId value)) after := by
        refine reflected.bind ?_ (fun _ _ _ => MonoM.refl _) (fun _ _ _ _ => MonoM.refl _)
        intro n ignored after pt' fr' done post residual bound
        exact ReflectAtFuel.ret residual (by simpa [EachSourceCells] using post)
      simpa only [pure_bind] using boundReflection
    exact composition.of_source (fun n => ⟨n + 1,by simp only [evalView]⟩)

theorem eachHeader_reflection_entry {cx : FnCtx} {le : LEnv}
    {input withHeader closed header : LS} {pt : Pt} {start hb : ValueId} {params : List ValueId}
    (hnew : newBlock [.data (.int .i64)] le input = ((hb,params),withHeader))
    (hterm : emitTerm (.br hb [start]) le withHeader = ((),closed))
    (hset : setCur (some hb) le closed = ((),header))
    (hpp : input.pp = some pt) (hext : ExtT header cx.fn.blocks)
    (generated : GeneratedBuilderState input) :
    GeneratedBuilderState header ∧ instAt cx.fn pt = some (.term (.br hb [start])) := by
  have hsetEq : header = { closed with cur := some hb } := by
    rw [setCur_run] at hset
    exact (Prod.mk.inj hset).2.symm
  have hextClosed : ExtT closed cx.fn.blocks := by simpa [hsetEq, ExtT] using hext
  have hextWith := hextClosed.of_adv (adv_emitTerm hterm)
  have hnewEq := hnew
  rw [newBlock1_run] at hnewEq
  obtain ⟨hids, hstate⟩ := Prod.mk.inj hnewEq
  obtain ⟨hhb, hparams⟩ := Prod.mk.inj hids
  have hcounter : params.headD 0 = input.vals.size := by rw [← hparams]; rfl
  have hsize : withHeader.vals.size = input.vals.size + 1 := by rw [← hstate]; simp
  have hstack : withHeader.stack = input.stack := by rw [← hstate]
  have hcur : withHeader.cur = input.cur := by rw [← hstate]
  obtain ⟨inputBlock, hcurInput, hlookupInput, hpointInput⟩ := LS.pp_some hpp
  have hltInput : pt.1 < input.blocks.size := (Array.getElem?_eq_some_iff.mp hlookupInput).1
  have hlookupWith : withHeader.blocks[pt.1]? = some inputBlock := by
    rw [← hstate]
    exact (getElem?_push_lt hltInput).trans hlookupInput
  have hppWith : withHeader.pp = some pt := by
    have h := LS.pp_eq (hcur.trans hcurInput) hlookupWith
    rw [← hpointInput] at h
    exact h
  obtain ⟨hvalsClosed, hstackClosed, _, hinst⟩ := emitTerm_facts hterm hppWith hextClosed
  have hheaderWith : withHeader.blocks[hb]? =
      some ⟨[(params.headD 0, .data (.int .i64))], #[]⟩ := by
    rw [hcounter, ← hhb, ← hstate]
    simp
  have hne : withHeader.cur ≠ some hb := by
    rw [hcur, hcurInput]
    intro he
    have hi := Option.some.inj he
    rw [← hhb] at hi
    exact Nat.ne_of_lt hltInput hi
  have hheaderClosed := (adv_emitTerm hterm).keep hb _ hne hheaderWith
  have generatedWith := generated.newBlock [.data (.int .i64)] hnew
  have generatedClosed := generatedWith.emitTerm (.br hb [start])
    (by
      intro target member
      simp only [Term.successors,List.mem_singleton] at member
      subst target
      exact (Array.getElem?_eq_some_iff.mp hheaderWith).1) hterm
  have generatedHeader := generatedClosed.setCur (some hb)
    (by intro current equal; have same := Option.some.inj equal; rw [← same]
        exact (Array.getElem?_eq_some_iff.mp hheaderClosed).1) hset
  exact ⟨generatedHeader,hinst⟩

theorem eachSampled_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {ls middle after : LS} {fr before : Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    {view result : ValueId} {vw : ViewVal} (fuel : Nat) (state : St)
    (post : Post cfg env cx ls fr middle before pt cells)
    (cell : before.vals[view]? = some (.view vw)) (regrow : Bool)
    (lowering : eachSampled regrow view le middle = (result,after)) (extension : ExtT after cx.fn.blocks) :
    ReflectAtFuel fuel cx pt before (fun _ => pure ()) (fun _ _ pt' fr' =>
      Post cfg env cx ls fr after fr' pt' (if regrow then cells else (result,.val (.int .i64 vw.len)) :: cells)) state := by
  cases regrow with
  | true =>
    simp only [eachSampled,ite_true,pure_run] at lowering
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj lowering
    exact ReflectAtFuel.ret fuel post
  | false =>
    simp only [eachSampled,Bool.false_eq_true,ite_false] at lowering ⊢
    exact leaf_def_keep_reflectAtFuel post lowering extension (by simp)
      (sourceFuel := 0) (fun _ => .val (.int .i64 vw.len))
      (by simpa using execPure_eachSampled cell)

end Goose.Lower
