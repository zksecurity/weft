/-!
# Domains, shapes and operands

A *domain* says what a share of a `T` is.  Programs are polymorphic in the
domain, so they can do nothing with a share except hand it to an
operation; the semantics instantiates the domain.

* `ideal`  — a share of a `T` is a `T`, a clear value is plain.  The
  semantics and every privacy statement live here.
* `erased` — a share is `()`.  This is what the adversary sees of a
  request: the clear components, and only the *shape* of the shared ones.
* `timed` (`Weft.Timed`) — shares and clear values carry the round at
  which they are available.

The operands and the response of an operation are each described by a
`Shape`, a closed language over types, so that their public part (`blank`)
is structural: a clear operand or a clear response is in the adversary's
record by shape, and a model cannot omit it.
-/
namespace Weft

/-- A domain: what a share of a `T` is, and what a clear value of a `T`
is.  Programs are polymorphic in it.  Clear values form an applicative
functor, so that a program computes on them (`e * d`) without seeing
inside; the only way to look at one is `Prog.look`. -/
structure Domain where
  share : Type → Type
  clear : Type → Type
  apply : Applicative clear

instance (D : Domain) : Applicative D.clear := D.apply

/-- Plain values, as an applicative. -/
abbrev Domain.plain : Applicative (fun T : Type => T) where
  map f x := f x
  pure x := x
  seq f x := f (x ())

/-- The ideal domain: a share is its value, a clear value is plain.
Semantics and privacy live here. -/
abbrev Domain.ideal : Domain := ⟨fun T => T, fun T => T, Domain.plain⟩

/-- `Domain.ideal.clear` unfolds to `fun T => T`, which the generic instance
does not match; name the instance at that type. -/
instance : Applicative Domain.ideal.clear := Domain.plain

/-- The erasure of a domain: shares become `()`, clear values stay what
they are.  What the adversary sees of a request in that domain. -/
abbrev Domain.erase (D : Domain) : Domain := ⟨fun _ => Unit, D.clear, D.apply⟩

/-- The erased ideal domain: shares are `()`, clear values are plain. -/
abbrev Domain.erased : Domain := Domain.ideal.erase

namespace Domain
variable {D : Domain} {T A B : Type}

@[simp] theorem ideal_map (f : A → B) (x : Domain.ideal.clear A) : (f <$> x : Domain.ideal.clear B) = f x := rfl
@[simp] theorem ideal_pure (a : A) : (pure a : Domain.ideal.clear A) = a := rfl
@[simp] theorem ideal_seq (f : Domain.ideal.clear (A → B)) (x : Unit → Domain.ideal.clear A) :
    (Seq.seq f x : Domain.ideal.clear B) = f (x ()) := rfl

/-! Arithmetic on clear values, in any domain: pointwise through the applicative. -/
instance [Add T] : Add (D.clear T) := ⟨fun a b => (· + ·) <$> a <*> b⟩
instance [Sub T] : Sub (D.clear T) := ⟨fun a b => (· - ·) <$> a <*> b⟩
instance [Mul T] : Mul (D.clear T) := ⟨fun a b => (· * ·) <$> a <*> b⟩
instance [Div T] : Div (D.clear T) := ⟨fun a b => (· / ·) <$> a <*> b⟩
instance [Neg T] : Neg (D.clear T) := ⟨fun a => Neg.neg <$> a⟩
instance [Inv T] : Inv (D.clear T) := ⟨fun a => Inv.inv <$> a⟩
instance {n : Nat} [OfNat T n] : OfNat (D.clear T) n := ⟨pure (OfNat.ofNat n)⟩
/-- A program-time value is a clear value available at once. -/
instance : Coe T (D.clear T) := ⟨pure⟩

end Domain

/-- The shape of the operands or of the response of an operation: a closed
language over types, so that its public part is structural.  Several
operands are a product (`⊗`); no operand is `unit`. -/
inductive Shape where
  | unit
  | clear (T : Type)
  | share (T : Type)
  | prod (a b : Shape)
  | vec (n : Nat) (a : Shape)
  | list (a : Shape)

namespace Shape

/-- A shape, interpreted in a domain.  Reducible, so that `D.share F` and
`Resp ι D o` unify wherever they are the same type. -/
@[reducible] def interp (D : Domain) : Shape → Type
  | unit => Unit
  | clear T => D.clear T
  | share T => D.share T
  | prod a b => a.interp D × b.interp D
  | vec n a => Fin n → a.interp D
  | list a => List (a.interp D)

/-! Pairs are taken apart by projections throughout, not by patterns: a
pattern here makes evaluation by `rfl` exponential in the number of
requests. -/

/-- The public part of a value: clear components are kept, shares become `()`. -/
def blank {D : Domain} : (s : Shape) → s.interp D → s.interp D.erase
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

@[simp] theorem blank_share {D : Domain} {T : Type} (x : D.share T) : (share T).blank x = () := rfl
@[simp] theorem blank_clear {D : Domain} {T : Type} (x : D.clear T) : (clear T).blank x = x := rfl
@[simp] theorem blank_unit {D : Domain} (x : unit.interp D) : unit.blank x = () := rfl
@[simp] theorem blank_prod {D : Domain} {a b : Shape} (p : a.interp D × b.interp D) :
    (prod a b).blank p = (a.blank p.1, b.blank p.2) := rfl
@[simp] theorem blank_vec {D : Domain} {n : Nat} {a : Shape} (f : Fin n → a.interp D) :
    (vec n a).blank f = fun i => a.blank (f i) := rfl
@[simp] theorem blank_list {D : Domain} {a : Shape} (xs : List (a.interp D)) :
    (list a).blank xs = xs.map a.blank := rfl

end Shape

/-- The product of two shapes, right-associative: `.share F ⊗ .share F ⊗ .clear F`
is `.prod (.share F) (.prod (.share F) (.clear F))`.  The operands of an
operation are one shape, so a binary operation takes a pair. -/
infixr:35 " ⊗ " => Shape.prod

end Weft
