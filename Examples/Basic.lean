import Weft

/-!
# Basic arithmetic programs

Programs parameterised by their domain and required functionalities,
with examples of output evaluation, timing, communication and views.
Realisation proofs are in `Examples.Beaver` and `Examples.Privacy`.
-/
namespace Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- Sum shares using linear operations. -/
def sumAll [Has (Lin F) fs] [OfNat F 0] : List (D.share F) → Prog fs.ops D (D.share F)
  | [] => const 0
  | [x] => pure x
  | x :: xs => do let s ← sumAll xs; add x s

/-- Multiply corresponding entries and sum the products.
The multiplications are independent;
`zip` truncates to the shorter input list. -/
def inner [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (xs ys : List (D.share F)) : Prog fs.ops D (D.share F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  sumAll ps

/-- Compute `(a * b) * c` with two dependent multiplications. -/
def mul3 [Has (Mult F) fs] (a b c : D.share F) : Prog fs.ops D (D.share F) := do
  let ab ← mul a b
  mul ab c

/-- A binary tree specifying the multiplication dependencies. -/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def prodTree [Has (Mult F) fs] : Tree (D.share F) → Prog fs.ops D (D.share F)
  | .leaf x => pure x
  | .node l r => do
    let a ← prodTree l
    let b ← prodTree r
    mul a b

/-- Reveal the product.
The view contains the multiplication event and the revealed value. -/
def openMul [Has (Mult F) fs] [Has (Reveal F) fs] (a b : D.share F) : Prog fs.ops D (D.clear F) := do
  let p ← mul a b
  reveal p

/-- Reveal both inputs before multiplying; this discloses more than the product. -/
def leakyMul [Has (Reveal F) fs] (a b : D.share F) : Prog fs.ops D (D.clear F) := do
  let x ← reveal a
  let y ← reveal b
  pure (x * y)

/-- Reveal the divisor and scale the shared numerator by its public reciprocal. -/
def divByOpened [Has (Lin F) fs] [Has (Reveal F) fs] [Div F] [OfNat F 1] (x d : D.share F) : Prog fs.ops D (D.share F) := do
  let dv ← reveal d          -- The divisor is disclosed.
  smul (1 / dv) x            -- Scalar multiplication waits for the reciprocal.

/-- Compute `a + [a < b] · (b - a)`.
The multiplication depends on the comparison result. -/
def maxOf [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]
    [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b : D.share F) : Prog fs.ops D (D.share F) := do
  let c ← lt a b
  let d ← sub b a
  let e ← mul c d
  add a e

/-- Add a public constant to an inner product. -/
def dotPlus [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (xs ys : List (D.share F)) (c : F) :
    Prog fs.ops D (D.share F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  let s ← sumAll ps
  let k ← const c
  add s k

/-- Horner evaluation with coefficients in increasing degree order.
This implementation uses one dependent multiplication per coefficient,
including the multiplication by the initial zero. -/
def horner [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (x : D.share F) : List (D.share F) → Prog fs.ops D (D.share F)
  | [] => const 0
  | a :: as => do
    let r ← horner x as
    let t ← mul r x
    add t a

/-- Generate a Beaver triple from two random shares and one multiplication. -/
def tripleFromRand [Fintype F] [Inhabited F] [Has (Rand F) fs] [Has (Mult F) fs] :
    Prog fs.ops D (D.share F × D.share F × D.share F) := do
  let a ← rand F
  let b ← rand F
  let c ← mul a b
  pure (a, b, c)

/-- Combine shares with successive powers of a public random challenge. -/
def randomCombination [Fintype F] [Inhabited F] [OfNat F 0] [Has (Lin F) fs] [Has (PubCoin F) fs]
    (xs : List (D.share F)) : Prog fs.ops D (D.share F) := do
  let r ← coin F
  let rec go (p : D.clear F) : List (D.share F) → Prog fs.ops D (D.share F)
    | [] => const 0
    | x :: xs => do
      let t ← smul p x
      let s ← go (p * r) xs
      add t s
  go r xs
end Programs

/-! ## Evaluation and cost examples -/

section Theorems
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

/-- Standard prices: multiplication `(1, 2)`, reveal `(1, 1)`, linear operations `(0, 0)`. -/
abbrev abb : MPC := [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]

-- Output evaluation.
example (a b c : F) : output (Std F).eval (mul3 (fs := Std F) (D := .ideal) a b c) = a * b * c := rfl

-- Two dependent multiplications from inputs available at round 0.
example (a b c : F) : delayOn (Std.timed F) (mul3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫) = 2 := rfl
-- The two subtrees are independent,
-- so the root is ready after two multiplication rounds.
example (a b c d : F) :
    delayOn (Std.timed F)
      (prodTree (fs := Std F) (D := .timed) (.node (.node (.leaf ⟪a⟫) (.leaf ⟪b⟫)) (.node (.leaf ⟪c⟫) (.leaf ⟪d⟫))))
      = 2 := rfl

-- Two multiplications at two communication units each.
example (a b c : F) : commOn (abb F).timed (mul3 (fs := (abb F).hybrid) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫) = 4 := rfl

-- The event list includes operation records as well as clear values.
example (a b : F) : view (Std F).eval (openMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.reveal F, ((), ()), a * b, ()⟩] := rfl
example (a b : F) : view (Std F).eval (leakyMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.reveal F, ((), ()), a, ()⟩, ⟨Std.reveal F, ((), ()), b, ()⟩] := rfl

-- Inner product with a public offset, followed by Horner evaluation.
section
variable [OfNat F 0]
example (a b c : F) (k : F) :
    output (Std F).eval (dotPlus (fs := Std F) (D := .ideal) [a, b] [c, c] k) = a * c + b * c + k := rfl
example (a b : F) (k : F) :
    delayOn (Std.timed F) (dotPlus (fs := Std F) (D := .timed) [⟪a⟫, ⟪b⟫] [⟪a⟫, ⟪b⟫] k) = 1 := rfl
-- Kernel evaluation avoids the elaborator's reduction overhead on this instance.
example : delayOn (Std.timed (Fin 7)) (horner (F := Fin 7) (fs := Std (Fin 7)) (D := .timed) ⟪3⟫ [⟪1⟫, ⟪2⟫, ⟪4⟫]) = 3 := by
  decide +kernel
example (x a₀ a₁ a₂ : F) :
    view (Std F).eval (horner (fs := Std F) (D := .ideal) x [a₀, a₁, a₂])
      = [⟨Std.lin F .const, (0, ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.lin F .add, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩,
         ⟨Std.lin F .add, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.lin F .add, ((), (), ()), (), ()⟩] := rfl
example : commOn (abb (Fin 7)).timed (horner (F := Fin 7) (fs := (abb (Fin 7)).hybrid) (D := .timed) ⟪3⟫ [⟪1⟫, ⟪2⟫, ⟪4⟫])
    = 6 := by decide +kernel
end

/-! ### Generating a triple from random shares -/
section
variable [Fintype F]
abbrev offline : MPC := [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Rand F).priced ⟨0, 0⟩]
example : (Sched.output (offline F).timed (tripleFromRand (F := F) (fs := (offline F).hybrid) (D := .timed))).2.2.time = 1 := rfl
example : commOn (offline F).timed (tripleFromRand (F := F) (fs := (offline F).hybrid) (D := .timed)) = 2 := rfl
end
end Theorems

end Weft.Examples.Basic
