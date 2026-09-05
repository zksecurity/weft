import Weft

/-!
# The basic programs, and the shape of the theorems

The programs from the design notes, written once against the
functionalities they need and polymorphic in the domain and the hybrid.
What one proves about each: correctness by evaluation, rounds in the timed
domain, communication on a price list, and the view.  Privacy, where it is
not trivial, is a realisation (`Examples.Beaver`, `Examples.Privacy`).
-/
namespace Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- Sum of shares: only linear operations, hence free and silent. -/
def sumAll [Has (Lin F) fs] [OfNat F 0] : List (D.sh F) → Prog fs.ops D (D.sh F)
  | [] => const 0
  | [x] => pure x
  | x :: xs => do let s ← sumAll xs; add x s

/-- Inner product: the multiplications are independent, so one round, then
a free sum.  Nothing says "parallel": the timed domain sees it. -/
def inner [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (xs ys : List (D.sh F)) : Prog fs.ops D (D.sh F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  sumAll ps

/-- Two dependent multiplications: two rounds. -/
def mul3 [Has (Mult F) fs] (a b c : D.sh F) : Prog fs.ops D (D.sh F) := do
  let ab ← mul a b
  mul ab c

/-- Balanced product tree: `depth` delay. -/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def prodTree [Has (Mult F) fs] : Tree (D.sh F) → Prog fs.ops D (D.sh F)
  | .leaf x => pure x
  | .node l r => do
    let a ← prodTree l
    let b ← prodTree r
    mul a b

/-- Reveal the product: the view is the product, and nothing else. -/
def openMul [Has (Mult F) fs] [Has (Reveal F) fs] (a b : D.sh F) : Prog fs.ops D F := do
  let p ← mul a b
  reveal p

/-- Reveal both inputs and multiply in the clear: correct, but not private. -/
def leakyMul [Has (Reveal F) fs] (a b : D.sh F) : Prog fs.ops D F := do
  let x ← reveal a
  let y ← reveal b
  pure (x * y)

/-- The reactive pattern: open, compute in the clear, insert back. -/
def divByOpened [Has (Lin F) fs] [Has (Reveal F) fs] [Div F] [OfNat F 1] (x d : D.sh F) : Prog fs.ops D (D.sh F) := do
  let dv ← reveal d          -- d is public information in this application
  smul (1 / dv) x            -- 1/d computed in the clear, multiplied back in

/-- `max a b = a + [a < b] · (b - a)`: a comparison round plus one multiplication round. -/
def maxOf [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]
    [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b : D.sh F) : Prog fs.ops D (D.sh F) := do
  let c ← lt a b
  let d ← sub b a
  let e ← mul c d
  add a e

/-- `⟨xs, ys⟩ + c`.  One round: the products in parallel, then free linear operations. -/
def dotPlus [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (xs ys : List (D.sh F)) (c : F) :
    Prog fs.ops D (D.sh F) := do
  let ps ← (xs.zip ys).mapM fun p => mul p.1 p.2
  let s ← sumAll ps
  let k ← const c
  add s k

/-- Horner evaluation of `Σ aᵢ xⁱ`: one multiplication per coefficient, each
depending on the last, so `n` rounds.  The honest cost of the schedule you
wrote; a parallel-prefix version would be `log n`. -/
def horner [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (x : D.sh F) : List (D.sh F) → Prog fs.ops D (D.sh F)
  | [] => const 0
  | a :: as => do
    let r ← horner x as
    let t ← mul r x
    add t a

/-- Triples from random shares and one secure multiplication: the offline phase as a program. -/
def tripleFromRand [Fintype F] [Inhabited F] [Has (Rand F) fs] [Has (Mult F) fs] :
    Prog fs.ops D (D.sh F × D.sh F × D.sh F) := do
  let a ← rand F
  let b ← rand F
  let c ← mul a b
  pure (a, b, c)

/-- A public coin used as a challenge: a random linear combination of shares. -/
def randomCombination [Fintype F] [Inhabited F] [OfNat F 0] [Has (Lin F) fs] [Has (PubCoin F) fs]
    (xs : List (D.sh F)) : Prog fs.ops D (D.sh F) := do
  let r ← coin F
  let rec go (p : F) : List (D.sh F) → Prog fs.ops D (D.sh F)
    | [] => const 0
    | x :: xs => do
      let t ← smul p x
      let s ← go (p * r) xs
      add t s
  go r xs
end Programs

/-! ## The shape of the theorems -/

section Theorems
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

/-- The black box, priced: multiplication one round and two units, reveal one round and one unit. -/
abbrev abb : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Mult F) ⟨1, 2⟩, MPC.const (Reveal F) ⟨1, 1⟩]

-- Functional correctness (against the ideal model), by evaluation.
example (a b c : F) : output (Std F).eval (mul3 (fs := Std F) (D := .ideal) a b c) = a * b * c := rfl

-- Delay, from data dependencies in the timed domain (inputs available at round 0).
example (a b c : F) : delayOn (Std.timed F) (mul3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫) = 2 := rfl
-- The product tree is written with plain binds and still costs its depth: the two
-- subtrees do not depend on each other, and the pass sees it.
example (a b c d : F) :
    delayOn (Std.timed F)
      (prodTree (fs := Std F) (D := .timed) (.node (.node (.leaf ⟪a⟫) (.leaf ⟪b⟫)) (.node (.leaf ⟪c⟫) (.leaf ⟪d⟫))))
      = 2 := rfl

-- Communication, on the price list.
example (a b c : F) : cost (abb F).eval (abb F).comm (mul3 (fs := (abb F).hybrid) (D := .ideal) a b c) = 4 := rfl

-- The view is computed, not asserted: what the adversary sees of a run.
example (a b : F) : view (Std F).eval (openMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.mult F, (), ()⟩, ⟨Std.reveal F, a * b, ()⟩] := rfl
example (a b : F) : view (Std F).eval (leakyMul (fs := Std F) (D := .ideal) a b)
    = [⟨Std.reveal F, a, ()⟩, ⟨Std.reveal F, b, ()⟩] := rfl

-- Standard-functionality programs: correctness, delay, silence.
section
variable [OfNat F 0]
example (a b c : F) (k : F) :
    output (Std F).eval (dotPlus (fs := Std F) (D := .ideal) [a, b] [c, c] k) = a * c + b * c + k := rfl
example (a b : F) (k : F) :
    delayOn (Std.timed F) (dotPlus (fs := Std F) (D := .timed) [⟪a⟫, ⟪b⟫] [⟪a⟫, ⟪b⟫] k) = 1 := rfl
example (x a₀ a₁ a₂ : F) :
    delayOn (Std.timed F) (horner (fs := Std F) (D := .timed) ⟪x⟫ [⟪a₀⟫, ⟪a₁⟫, ⟪a₂⟫]) = 3 := rfl
example (x a₀ a₁ a₂ : F) :
    view (Std F).eval (horner (fs := Std F) (D := .ideal) x [a₀, a₁, a₂])
      = [⟨Std.lin F (.const 0), (), ()⟩, ⟨Std.mult F, (), ()⟩, ⟨Std.lin F .add, (), ()⟩, ⟨Std.mult F, (), ()⟩,
         ⟨Std.lin F .add, (), ()⟩, ⟨Std.mult F, (), ()⟩, ⟨Std.lin F .add, (), ()⟩] := rfl
example (x a₀ a₁ a₂ : F) :
    cost (abb F).eval (abb F).comm (horner (fs := (abb F).hybrid) (D := .ideal) x [a₀, a₁, a₂]) = 6 := rfl
end

/-! ### The offline phase, timed: a triple costs one multiplication round when assembled from random shares -/
section
variable [Fintype F]
abbrev offline : MPC := [MPC.const (Lin F) ⟨0, 0⟩, MPC.const (Mult F) ⟨1, 2⟩, MPC.const (Rand F) ⟨0, 0⟩]
example : (Sched.output (offline F).timed (tripleFromRand (F := F) (fs := (offline F).hybrid) (D := .timed))).2.2.time = 1 := rfl
example : cost (offline F).eval (offline F).comm (tripleFromRand (F := F) (fs := (offline F).hybrid) (D := .ideal)) = 2 := rfl
end
end Theorems

end Weft.Examples.Basic
