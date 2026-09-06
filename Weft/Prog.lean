import Weft.Interface

/-!
# Programs: the free monad over an interface

A program is a tree of requests with Lean continuations.  It opens values,
computes in the clear and branches on public values, so "program" rather
than "circuit"; the straight-line case is a circuit.  Programs are
polymorphic in the domain, which is what keeps them from looking inside a
share (see `Weft.Program` for the check that makes this a guarantee).
-/
namespace Weft

/-- The free monad over an interface: `pure`; one request and a
continuation on its response; or one look at a clear value and a
continuation on what it holds.  `look` is the only way to turn a
`D.clear T` into a `T`, so it is where a program's control flow depends on
an opened value, and the timed domain sees it (`Weft.Timed`).  The ideal
semantics ignores it. -/
inductive Prog (ι : Interface) (D : Domain) : Type → Type 1 where
  | pure {α : Type} : α → Prog ι D α
  | call {α : Type} (r : Req ι D) : (Resp ι D r.op → Prog ι D α) → Prog ι D α
  | look {α T : Type} (c : D.clear T) : (T → Prog ι D α) → Prog ι D α

namespace Prog
variable {ι κ : Interface} {D : Domain} {α β : Type}

def bind : Prog ι D α → (α → Prog ι D β) → Prog ι D β
  | .pure a, f => f a
  | .call r k, f => .call r fun y => bind (k y) f
  | .look c k, f => .look c fun v => bind (k v) f

instance : Monad (Prog ι D) where
  pure := Prog.pure
  bind := Prog.bind

@[simp] theorem bind_eq (c : Prog ι D α) (f : α → Prog ι D β) : c >>= f = Prog.bind c f := rfl
@[simp] theorem pure_eq (a : α) : (pure a : Prog ι D α) = Prog.pure a := rfl
@[simp] theorem bind_pure' (a : α) (f : α → Prog ι D β) : Prog.bind (.pure a) f = f a := rfl
@[simp] theorem bind_call (r : Req ι D) (k : Resp ι D r.op → Prog ι D α) (f : α → Prog ι D β) :
    Prog.bind (.call r k) f = .call r fun y => Prog.bind (k y) f := rfl
@[simp] theorem bind_look {T : Type} (c : D.clear T) (k : T → Prog ι D α) (f : α → Prog ι D β) :
    Prog.bind (.look c k) f = .look c fun v => Prog.bind (k v) f := rfl

theorem bind_pure (c : Prog ι D α) : Prog.bind c .pure = c := by
  induction c with
  | pure a => rfl
  | call r k ih => simp [ih]
  | look c k ih => simp [ih]

theorem bind_assoc {γ : Type} (c : Prog ι D α) (f : α → Prog ι D β) (g : β → Prog ι D γ) :
    Prog.bind (Prog.bind c f) g = Prog.bind c fun a => Prog.bind (f a) g := by
  induction c with
  | pure a => rfl
  | call r k ih => simp [ih]
  | look c k ih => simp [ih]

instance : LawfulMonad (Prog ι D) :=
  LawfulMonad.mk' _ bind_pure (fun _ _ => rfl) fun c f g => bind_assoc c f g

/-- Issue one request of the interface itself. -/
def req (r : Req ι D) : Prog ι D (Resp ι D r.op) := .call r .pure

/-- Realise every request of `ι` by a program over `κ` (a handler). -/
def handle (h : (r : Req ι D) → Prog κ D (Resp ι D r.op)) : Prog ι D α → Prog κ D α
  | .pure a => .pure a
  | .call r k => bind (h r) fun y => handle h (k y)
  | .look c k => .look c fun v => handle h (k v)

@[simp] theorem handle_pure (h : (r : Req ι D) → Prog κ D (Resp ι D r.op)) (a : α) :
    handle h (.pure a : Prog ι D α) = .pure a := rfl
@[simp] theorem handle_call (h : (r : Req ι D) → Prog κ D (Resp ι D r.op)) (r : Req ι D)
    (k : Resp ι D r.op → Prog ι D α) :
    handle h (.call r k) = bind (h r) fun y => handle h (k y) := rfl
@[simp] theorem handle_look (h : (r : Req ι D) → Prog κ D (Resp ι D r.op)) {T : Type} (c : D.clear T)
    (k : T → Prog ι D α) :
    handle h (.look c k) = .look c fun v => handle h (k v) := rfl

end Prog
end Weft
