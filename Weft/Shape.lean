/-!
# Domains, shapes and operands

A domain chooses the representation of shared and clear values.
Programs are polymorphic in the domain;
`Weft.Program` checks that implementations cannot inspect shares.

* `ideal` represents both shared and clear values by their underlying types.
* `erased` replaces shares with `Unit` and preserves clear values.
* `timed` attaches an availability round to both kinds of value.

`Shape` describes operands and responses.
Its `blank` operation removes shared values from the adversary's record,
while preserving clear values and the surrounding structure.
-/
namespace Weft

/-- Representations of shared and clear values.
The applicative supports computation on clear values;
`Prog.look` exposes a clear value to the program's control flow. -/
structure Domain where
  share : Type → Type
  clear : Type → Type
  apply : Applicative clear

instance (D : Domain) : Applicative D.clear := D.apply

/-- The identity applicative. -/
abbrev Domain.plain : Applicative (fun T : Type => T) where
  map f x := f x
  pure x := x
  seq f x := f (x ())

/-- Interpret shares and clear values as their underlying values. -/
abbrev Domain.ideal : Domain := ⟨fun T => T, fun T => T, Domain.plain⟩

/-- The generic instance does not match the unfolded type `fun T => T`. -/
instance : Applicative Domain.ideal.clear := Domain.plain

/-- Replace shares with `Unit` and preserve clear values. -/
abbrev Domain.erase (D : Domain) : Domain := ⟨fun _ => Unit, D.clear, D.apply⟩

/-- The erased ideal domain: shares are `()`, clear values are plain. -/
abbrev Domain.erased : Domain := Domain.ideal.erase

namespace Domain
variable {D : Domain} {T A B : Type}

@[simp] theorem ideal_map (f : A → B) (x : Domain.ideal.clear A) : (f <$> x : Domain.ideal.clear B) = f x := rfl
@[simp] theorem ideal_pure (a : A) : (pure a : Domain.ideal.clear A) = a := rfl
@[simp] theorem ideal_seq (f : Domain.ideal.clear (A → B)) (x : Unit → Domain.ideal.clear A) :
    (Seq.seq f x : Domain.ideal.clear B) = f (x ()) := rfl

/-! Lift arithmetic through the clear-value applicative. -/
instance [Add T] : Add (D.clear T) := ⟨fun a b => (· + ·) <$> a <*> b⟩
instance [Sub T] : Sub (D.clear T) := ⟨fun a b => (· - ·) <$> a <*> b⟩
instance [Mul T] : Mul (D.clear T) := ⟨fun a b => (· * ·) <$> a <*> b⟩
instance [Div T] : Div (D.clear T) := ⟨fun a b => (· / ·) <$> a <*> b⟩
instance [Neg T] : Neg (D.clear T) := ⟨fun a => Neg.neg <$> a⟩
instance [Inv T] : Inv (D.clear T) := ⟨fun a => Inv.inv <$> a⟩
instance {n : Nat} [OfNat T n] : OfNat (D.clear T) n := ⟨pure (OfNat.ofNat n)⟩
/-- Embed a value using `pure`. -/
instance : Coe T (D.clear T) := ⟨pure⟩

end Domain

/-- Operand and response shapes,
with explicit shared and clear components. -/
inductive Shape where
  | unit
  | clear (T : Type)
  | share (T : Type)
  | prod (a b : Shape)
  | vec (n : Nat) (a : Shape)
  | list (a : Shape)

namespace Shape

/-- Interpret a shape in `D`.
Reducibility lets response types unify with their component types. -/
@[reducible] def interp (D : Domain) : Shape → Type
  | unit => Unit
  | clear T => D.clear T
  | share T => D.share T
  | prod a b => a.interp D × b.interp D
  | vec n a => Fin n → a.interp D
  | list a => List (a.interp D)

/-- The public part of a response: clear components are kept, shares become `()`. -/
def blank {D : Domain} : (s : Shape) → s.interp D → s.interp D.erase
  | unit, _ => ()
  | clear _, x => x
  | share _, _ => ()
  | prod a b, p => (a.blank p.1, b.blank p.2)
  | vec _ a, f => fun i => a.blank (f i)
  | list a, xs => xs.map a.blank

/-- Whether the shape contains a `clear` constructor. -/
def hasClear : Shape → Bool
  | unit => false
  | clear _ => true
  | share _ => false
  | prod a b => a.hasClear || b.hasClear
  | vec _ a => a.hasClear
  | list a => a.hasClear

/-- Shapes containing no clear components.
Container structure, e.g. list length, is still public. -/
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

/-- A tuple of operands with the given shapes. -/
@[reducible] def Operands (D : Domain) : List Shape → Type
  | [] => Unit
  | s :: ss => s.interp D × Operands D ss

namespace Operands

/-! Use projections to unpack operand pairs.
Pattern matching here causes exponential reduction time under `rfl`. -/

/-- Map a shape-indexed transformation over the operands. -/
def map {D E : Domain} (f : (s : Shape) → s.interp D → s.interp E) :
    {ss : List Shape} → Operands D ss → Operands E ss
  | [], _ => ()
  | s :: _, p => (f s p.1, map f p.2)

/-- The public part of the operands: clear operands are kept, shares become `()`. -/
def blank {D : Domain} : {ss : List Shape} → Operands D ss → Operands D.erase ss
  | [], _ => ()
  | s :: _, p => (s.blank p.1, blank p.2)

@[simp] theorem blank_nil {D : Domain} (a : Operands D []) : blank a = () := rfl
@[simp] theorem blank_cons {D : Domain} {s : Shape} {ss : List Shape} (a : Operands D (s :: ss)) :
    blank a = (s.blank a.1, blank a.2) := rfl

end Operands

end Weft
