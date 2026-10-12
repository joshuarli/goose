import Goose.Core.Syntax
import Goose.Share.Rename
import Goose.Share.Equal

/-!
How a call resolves, and when two modules run the same program.

A call names a context; the context names an implementation; the
implementation's body runs. `Simulates m m' r` says that `m'` resolves every
call the way `m` does, up to renaming the callees of the body by `r`, and
initializes the same globals. It is exactly what `eval` reads of a module, so
it is the hypothesis of the proof that results agree.
-/

namespace Goose.Share

open Goose.Core

/-- The implementation that a call naming context `c` runs. A missing context
and a context naming a missing implementation both make the call unbound. -/
def resolve (m : Module) (c : ContextId) : Option Impl :=
  (m.contexts[c]?).bind fun ctx => m.impls[ctx.impl]?

/-- `m'` runs `m`'s program with every callee renamed by `r`: calls resolve to
the renamed implementation, the entry does too, and the globals have the same
renamed initializers. -/
structure Simulates (m m' : Module) (r : CtxMap) : Prop where
  resolves : ∀ c, resolve m' (r c) = (resolve m c).map (renImpl r)
  entry : resolve m' m'.entry = (resolve m m.entry).map (renImpl r)
  globalCount : m'.globals.size = m.globals.size
  globalInit : ∀ g : GlobalId, (m'.globals[g]?).map Global.init = (m.globals[g]?).map (fun (gl : Global) => renExpr r gl.init)

/-- `m'` is the quotient of `m` by `q`, a map on implementation indices, with the
callees of every body renamed by `r`.

* The header tables, the entry and the contexts' indices are unchanged;
  each context of `m'` is the context of `m` with its implementation index
  mapped by `q`. The root annotations are kept as they are.
* Every implementation a context of `m` names is, in `m`, the body that
  `m'` holds at `q` of its index, with callees renamed by `r`. Two
  implementations that `q` identifies therefore have equal bodies once their
  callees are renamed, and the renaming sends a context to one that `m'`
  maps to the same implementation (`callees`). Implementations no context
  names cannot be reached by a run, so nothing is demanded of them.
* Globals are those of `m` with initializers renamed by `r`. -/
structure Quotient (m m' : Module) (q : ImplId → ImplId) (r : CtxMap) : Prop where
  files : m'.files = m.files
  types : m'.types = m.types
  origins : m'.origins = m.origins
  entry : m'.entry = m.entry
  globals : m'.globals = m.globals.map (renGlobal r)
  contextCount : m'.contexts.size = m.contexts.size
  contexts : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
    m'.contexts[c]? = some { ctx with impl := q ctx.impl }
  impls : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
    m'.impls[q ctx.impl]? = (m.impls[ctx.impl]?).map (renImpl r)
  callees : ∀ c : ContextId,
    (m'.contexts[r c]?).map Context.impl = (m'.contexts[c]?).map Context.impl

/-! ### The executable check -/

/-- Pairwise comparison of two lists of equal length. -/
def allZip {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allZip f as bs
  | _, _ => false

def eqOptImpl : Option Impl → Option Impl → Bool
  | none, none => true
  | some a, some b => eqImpl a b
  | _, _ => false

/-- Accepts exactly when `m'` is the quotient of `m` by the index map `qt`
(an index outside the table maps to itself) with callees renamed by the
context map `rt` (likewise). `qt` and `rt` are untrusted witnesses: a wrong
one makes the check fail, never succeed. -/
def checkQuotient (m m' : Module) (qt : Array ImplId) (rt : Array ContextId) : Bool :=
  let q : ImplId → ImplId := fun f => qt.getD f f
  let r : CtxMap := fun c => rt.getD c c
  (m'.files == m.files && m'.types == m.types && m'.origins == m.origins &&
    m'.entry == m.entry) &&
  allZip (fun g g' => eqGlobal (renGlobal r g) g') m.globals.toList m'.globals.toList &&
  allZip (fun ctx ctx' => ctx' == { ctx with impl := q ctx.impl })
    m.contexts.toList m'.contexts.toList &&
  m.contexts.toList.all (fun ctx =>
    eqOptImpl (m'.impls[q ctx.impl]?) ((m.impls[ctx.impl]?).map (renImpl r))) &&
  rt.size == m.contexts.size &&
  (List.range m.contexts.size).all (fun c =>
    (m'.contexts[r c]?).map Context.impl == (m'.contexts[c]?).map Context.impl)

end Goose.Share
