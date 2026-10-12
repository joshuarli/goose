import Std.Data.HashMap
import Goose.Share.Quotient
import Goose.Share.Writer

/-!
Proposing a quotient, and rebuilding the witnesses of a given one.

Nothing here is trusted. A proposal is a module together with the index and
context tables `checkQuotient` needs, and it is only used once the checker
accepts it, so a defect here shows up as a rejection, never as a wrong merge.
-/

namespace Goose.Share

open Goose.Core

/-- For each context, the first context whose implementation lies in the same
class. `classOf` gives the class of an implementation; a context naming a
missing implementation represents itself. -/
def representatives (m : Module) (classOf : ImplId → Nat) : Array ContextId := Id.run do
  let mut first : Std.HashMap Nat ContextId := {}
  let mut out : Array ContextId := Array.mkEmpty m.contexts.size
  for h : c in [0:m.contexts.size] do
    let ctx := m.contexts[c]'(Membership.get_elem_helper h rfl)
    if ctx.impl < m.impls.size then
      let k := classOf ctx.impl
      match first[k]? with
      | some c0 => out := out.push c0
      | none =>
        first := first.insert k c
        out := out.push c
    else out := out.push c
  return out

/-- The identity on implementation indices, then each implementation a context
names sent to the one the shared module's context at the same index names. -/
def reconstructImplMap (m m' : Module) : Array ImplId := Id.run do
  let mut qt : Array ImplId := Array.ofFn (n := m.impls.size) fun i => i.val
  for h : c in [0:m.contexts.size] do
    let ctx := m.contexts[c]'(Membership.get_elem_helper h rfl)
    if let some ctx' := m'.contexts[c]? then
      if ctx.impl < qt.size then qt := qt.set! ctx.impl ctx'.impl
  return qt

/-- Each context sent to the first context of the shared module that runs the
same implementation. -/
def reconstructContextMap (m m' : Module) : Array ContextId := Id.run do
  let mut first : Std.HashMap ImplId ContextId := {}
  let mut out : Array ContextId := Array.mkEmpty m.contexts.size
  for c in [0:m.contexts.size] do
    match m'.contexts[c]? with
    | none => out := out.push c
    | some ctx' =>
      match first[ctx'.impl]? with
      | some c0 => out := out.push c0
      | none =>
        first := first.insert ctx'.impl c
        out := out.push c
  return out

/-- A proposed quotient and the witnesses that justify it. -/
structure Proposal where
  shared : Module
  implMap : Array ImplId
  contextMap : Array ContextId

/-- Group implementations by equal bodies, with callees compared through the
current grouping, and refine until the grouping is stable. Starting from one
group makes the result the coarsest grouping that is consistent with itself,
so a call cycle through several implementations merges as a whole. -/
def classify (m : Module) : Array Nat := Id.run do
  let n := m.impls.size
  let ty := Write.tyIndex m.types
  let mut cls : Array Nat := Array.replicate n 0
  let mut count := if n == 0 then 0 else 1
  for _ in [0:n + 1] do
    let reps := representatives m (fun f => cls.getD f 0)
    let r : CtxMap := fun c => reps.getD c c
    let mut ids : Std.HashMap String Nat := {}
    let mut next : Array Nat := Array.mkEmpty n
    for h : f in [0:n] do
      let impl := m.impls[f]'(Membership.get_elem_helper h rfl)
      let key := s!"{cls.getD f 0}|{Write.impl ty (renImpl r impl)}"
      match ids[key]? with
      | some k => next := next.push k
      | none =>
        let k := ids.size
        ids := ids.insert key k
        next := next.push k
    cls := next
    if ids.size == count then break
    count := ids.size
  return cls

/-- Merge every group of implementations with equal bodies. A group whose
members are already equal keeps that body untouched, so callers and callees
keep the contexts they name; only a group whose members differ in naming
mergeable callees has its body renamed, to one context per group of equal
callees. Fails when a context names an implementation that does not exist,
which has no shared counterpart. -/
def propose (m : Module) : Except String Proposal := do
  for ctx in m.contexts do
    if ctx.impl ≥ m.impls.size then
      throw s!"a context of {ctx.decl} names implementation {ctx.impl}, which does not exist"
  let cls := classify m
  let reps := representatives m (fun f => cls.getD f 0)
  let r : CtxMap := fun c => reps.getD c c
  let classes := cls.foldl (fun acc k => max acc (k + 1)) 0
  -- the smallest member of each group is the one whose body is kept
  let mut firstMember : Array ImplId := Array.replicate classes 0
  let mut seen : Array Bool := Array.replicate classes false
  for f in [0:m.impls.size] do
    let k := cls.getD f 0
    if !seen.getD k false then
      seen := seen.set! k true
      firstMember := firstMember.set! k f
  let impls ← firstMember.mapIdxM fun k f => do
    let some keep := m.impls[f]? | throw s!"internal error: no implementation {f}"
    let unchanged := (List.range m.impls.size).all fun g =>
      cls.getD g 0 != k || (match m.impls[g]? with
        | some other => eqImpl keep other
        | none => false)
    pure (if unchanged then keep else renImpl r keep)
  let shared : Module :=
    { m with
      impls
      contexts := m.contexts.map fun ctx => { ctx with impl := cls.getD ctx.impl 0 } }
  return { shared, implMap := cls, contextMap := reps }

end Goose.Share
