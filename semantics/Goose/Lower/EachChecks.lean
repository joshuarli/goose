import Goose.Lower.Each
import Goose.Core.Validate
import Goose.GIR.Validate

namespace Goose.Lower.EachChecks

open Goose.Core Goose.GIR

def ownerType (grow : Bool) : Ty :=
  if grow then .grow (.int .i64) else .limited (.int .i64) 2

def eachModule (grow byRef : Bool) (tail : List Stmt) : Core.Module :=
  let element : Expr := if byRef then .read (.deref (.read (.var 0))) else .read (.var 0)
  let mutate : Stmt := if byRef then .assign (.deref (.read (.var 0))) (.lit .i64 100) 0
    else .assign (.var 0) (.lit .i64 100) 0
  let adjust : Stmt := if grow then
    .ifS (.cmp .eq (.read (.var 1)) (.lit .i64 0))
      (.mk 2 [.expr (.push (.global 0) (.lit .i64 7) (some 0)) 0] none) none 0
    else .clear (.global 0) 0
  let vars : Array LocalVar :=
    #[⟨"element", if byRef then .ref .mutable (.int .i64) else .int .i64, .mutable, 1, 0⟩,
      ⟨"index", .int .i64, .mutable, 1, 0⟩]
  let body : Core.Block := .mk 1
    ([.print [.expr element] 0, adjust, mutate, .print [.expr element] 0] ++ tail) none
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := vars,
      body := .mk 0 [.forEach 0 (some 1) (.of (.global 0)) byRef body 0] none,
      summary := .unknown }
  { files := #["each.goose"], types := #[.int .i64, ownerType grow],
    globals := #[⟨"owner", ownerType grow, .mutable,
      .arrLit (ownerType grow) (if grow then [.lit .i64 9] else [.lit .i64 9, .lit .i64 7]), 0⟩],
    impls := #[main], contexts := #[⟨0, "main", if byRef then [(0, [.global 0])] else [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "each"⟩], profile := .shrink }

#guard [false, true].all fun grow => [false, true].all fun byRef =>
  match Core.validate (eachModule grow byRef []), GIR.validate (lower (eachModule grow byRef [])) with
  | .ok _, .ok _ => true
  | _, _ => false

def actualRuns (m : Core.Module) (trace : String) : Bool :=
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 80 profile m, GIR.run 500 profile (lower m) with
    | .done .returned a, .done .returned b => a == trace && b == trace
    | _, _ => false

#guard actualRuns (eachModule false false []) "9\n100\n7\n100\n"
#guard actualRuns (eachModule false true []) "9\n100\n7\n100\n"
#guard actualRuns (eachModule true false []) "9\n100\n7\n100\n"
#guard actualRuns (eachModule true true []) "9\n100\n7\n100\n"
#guard actualRuns (eachModule false false [.cont 0]) "9\n100\n7\n100\n"
#guard actualRuns (eachModule true true [.cont 0]) "9\n100\n7\n100\n"
#guard actualRuns (eachModule false true [.brk 0]) "9\n100\n"
#guard actualRuns (eachModule true false [.ret none 0]) "9\n100\n"

def sourceOnceModule (byRef : Bool) : Core.Module :=
  let m := eachModule true byRef []
  { m with impls := m.impls.map fun impl =>
    { impl with vars := impl.vars.map (fun lv => { lv with scope := 2 }), body := match impl.body with
      | .mk sc [.forEach x idx _ ref body org] value =>
        .mk sc [.forEach x idx (.val (.blockE (.mk 1 [.print [.text "sample"] 0]
          (some (.slice .mutable (.of (.global 0)) .omitted .omitted 0))))) ref
            (.mk 2 (body.stmts.map fun stmt => match stmt with
              | .ifS cond (.mk _ stmts value) none org => .ifS cond (.mk 3 stmts value) none org
              | stmt => stmt) body.value) org] value
      | body => body } }

#guard [false, true].all fun byRef =>
  match Core.validate (sourceOnceModule byRef), GIR.validate (lower (sourceOnceModule byRef)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard actualRuns (sourceOnceModule false) "sample\n9\n100\n"
#guard actualRuns (sourceOnceModule true) "sample\n9\n100\n"

def ownerContents (s : St) (grow : Bool) (first second : Int) : Bool :=
  s.store.roots.size == 1 && match s.store.roots[RootInst.global 0]? with
  | some (.limited _ 2 slots 0) => !grow && match slots[0]?, slots[1]? with
    | some (Val.int IntTy.i64 a), some (Val.int IntTy.i64 b) => a == first && b == second
    | _, _ => false
  | some (.resizable _ slots) => grow && slots.size == 2 && match slots[0]?, slots[1]? with
    | some (Val.int IntTy.i64 a), some (Val.int IntTy.i64 b) => a == first && b == second
    | _, _ => false
  | _ => false

def actualOwnerRuns (grow byRef : Bool) : Bool :=
  let m := eachModule grow byRef []
  let first := if byRef then 100 else 9
  let second := if byRef then 100 else 7
  [NumProfile.release, .debug].all fun profile =>
    match Core.runModule 80 ⟨profile, m⟩ St.initial,
      GIR.runModule 500 ⟨profile, lower m⟩ St.initial with
    | .ok _ a, .ok _ b => ownerContents a grow first second && ownerContents b grow first second
    | _, _ => false

#guard [false, true].all fun grow => [false, true].all fun byRef => actualOwnerRuns grow byRef

end Goose.Lower.EachChecks
