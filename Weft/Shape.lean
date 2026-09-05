/-!
# Domains, shapes and operands

A *domain* says what a share of a `T` is.  Programs are polymorphic in the
domain, so they can do nothing with a share except hand it to an
operation; the semantics instantiates the domain.

* `ideal`  — a share of a `T` is a `T`.  The semantics and every privacy
  statement live here.
* `erased` — a share is `()`.  This is what the adversary sees of a
  response: the clear components, and only the *shape* of the shared ones.

The response of an operation is described by a `Shape`, a closed language
over types, so that its public part (`blank`) is structural: a model
cannot return a clear value and omit it from the view.
-/
namespace Weft

/-- A domain: what a share of a `T` is.  Programs are polymorphic in it. -/
structure Domain where
  sh : Type → Type

/-- The ideal domain: a share is its value.  Semantics and privacy live here. -/
abbrev Domain.ideal : Domain := ⟨fun T => T⟩

/-- The erased domain: a share is `()`.  What the adversary sees of a response. -/
abbrev Domain.erased : Domain := ⟨fun _ => Unit⟩

/-- The shape of a response: a closed language over types, so that the
public part of a response is structural. -/
inductive Shape where
  | unit
  | clear (T : Type)
  | share (T : Type)
  | prod (a b : Shape)
  | vec (n : Nat) (a : Shape)
  | list (a : Shape)

namespace Shape

/-- A shape, interpreted in a domain.  Reducible, so that `D.sh F` and
`Resp ι D o` unify wherever they are the same type. -/
@[reducible] def interp (D : Domain) : Shape → Type
  | unit => Unit
  | clear T => T
  | share T => D.sh T
  | prod a b => a.interp D × b.interp D
  | vec n a => Fin n → a.interp D
  | list a => List (a.interp D)

/-- The public part of a response: clear components are kept, shares become `()`. -/
def blank {D : Domain} : (s : Shape) → s.interp D → s.interp .erased
  | unit, _ => ()
  | clear _, x => x
  | share _, _ => ()
  | prod a b, p => (a.blank p.1, b.blank p.2)
  | vec _ a, f => fun i => a.blank (f i)
  | list a, xs => xs.map a.blank

/-- Whether a response has a clear component (a program may branch on it,
so in the timed domain it raises the reveal clock). -/
def hasClear : Shape → Bool
  | unit => false
  | clear _ => true
  | share _ => false
  | prod a b => a.hasClear || b.hasClear
  | vec _ a => a.hasClear
  | list a => a.hasClear

/-- A shape without clear components: blanking it is trivial. -/
def Hidden : Shape → Prop
  | unit => True
  | clear _ => False
  | share _ => True
  | prod a b => a.Hidden ∧ b.Hidden
  | vec _ a => a.Hidden
  | list a => a.Hidden

@[simp] theorem blank_share {D : Domain} {T : Type} (x : D.sh T) : (share T).blank x = () := rfl
@[simp] theorem blank_clear {D : Domain} {T : Type} (x : T) : (clear T).blank (D := D) x = x := rfl
@[simp] theorem blank_unit {D : Domain} (x : unit.interp D) : unit.blank x = () := rfl
@[simp] theorem blank_prod {D : Domain} {a b : Shape} (p : a.interp D × b.interp D) :
    (prod a b).blank p = (a.blank p.1, b.blank p.2) := rfl
@[simp] theorem blank_vec {D : Domain} {n : Nat} {a : Shape} (f : Fin n → a.interp D) :
    (vec n a).blank f = fun i => a.blank (f i) := rfl
@[simp] theorem blank_list {D : Domain} {a : Shape} (xs : List (a.interp D)) :
    (list a).blank xs = xs.map a.blank := rfl

end Shape

/-- The operands of a request: one share per entry of the operand list.
Operands are shares only; clear arguments belong to the operation. -/
@[reducible] def Operands (D : Domain) : List Type → Type
  | [] => Unit
  | T :: Ts => D.sh T × Operands D Ts

namespace Operands

/-! Pairs are taken apart by projections throughout, not by patterns: a
pattern here makes evaluation by `rfl` exponential in the number of
requests. -/

/-- Map a domain transformation over the operands. -/
def map {D E : Domain} (f : ∀ {T}, D.sh T → E.sh T) : {Ts : List Type} → Operands D Ts → Operands E Ts
  | [], _ => ()
  | _ :: _, p => (f p.1, map f p.2)

/-- Collect something from every operand. -/
def toList {D : Domain} {β : Type} (f : ∀ {T}, D.sh T → β) : {Ts : List Type} → Operands D Ts → List β
  | [], _ => []
  | _ :: _, p => f p.1 :: toList f p.2

/-- `n` operands of one type, from a vector. -/
def ofFin {D : Domain} {T : Type} : (n : Nat) → (Fin n → D.sh T) → Operands D (List.replicate n T)
  | 0, _ => ()
  | n + 1, f => (f 0, ofFin n (fun i => f i.succ))

/-- `n` operands of one type, as a vector. -/
def toFin {D : Domain} {T : Type} : (n : Nat) → Operands D (List.replicate n T) → Fin n → D.sh T
  | 0, _ => fun i => i.elim0
  | n + 1, p => Fin.cases p.1 (toFin n p.2)

/-- Operands of one type, from a list (the operand list is the list's length). -/
def ofList {D : Domain} {T : Type} : (xs : List (D.sh T)) → Operands D (List.replicate xs.length T)
  | [] => ()
  | x :: xs => (x, ofList xs)

end Operands

end Weft
