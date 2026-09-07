import Weft
import Examples.Basic
import Examples.Beaver

/-!
# Arithmetic program examples

Matrix products, product trees, public control flow, sorting and conversions,
followed by evaluation and timing checks on concrete inputs.
Programs specify their required functionalities through `Has` instances.
-/
namespace Weft.Examples.Gallery
open Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-! ## Matrix–vector product -/

/-- Apply `inner` to each row; all row computations are independent. -/
def matVec [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (rows : List (List (D.share F))) (v : List (D.share F)) :
    Prog fs.ops D (List (D.share F)) :=
  rows.mapM fun row => inner row v

/-! ## Product by pairwise reduction -/

/-- Multiply adjacent pairs and retain any unpaired final element. -/
def pairwise [Has (Mult F) fs] : List (D.share F) → Prog fs.ops D (List (D.share F))
  | a :: b :: rest => do
    let p ← mul a b
    let ps ← pairwise rest
    pure (p :: ps)
  | xs => pure xs

/-- Reduce adjacent pairs until one product remains.
For a nonempty list of length `n`, the multiplication depth is `⌈log₂ n⌉`.
The public list length supplies recursion fuel. -/
def prodAll [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (xs : List (D.share F)) : Prog fs.ops D (D.share F) :=
  go xs.length xs
where
  go : Nat → List (D.share F) → Prog fs.ops D (D.share F)
    | _, [x] => pure x
    | 0, _ => const 1
    | n + 1, xs => do
      let ys ← pairwise xs
      go n ys

/-! ## Public exponentiation -/

/-- Square-and-multiply with exponent bits in least-significant-first order.
The public exponent determines the operation sequence. -/
def expBits [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (x : D.share F) : List Bool → Prog fs.ops D (D.share F)
  | [] => const 1
  | [b] => if b then pure x else const 1
  | b :: bs => do
    let h ← expBits x bs
    let sq ← mul h h
    if b then mul sq x else pure sq

/-- Binary digits in least-significant-first order.
Recursion on fuel keeps evaluation reducible. -/
def bits (n : Nat) : List Bool := go n n
where
  go : Nat → Nat → List Bool
    | 0, _ => []
    | fuel + 1, n => if n = 0 then [] else (n % 2 = 1) :: go fuel (n / 2)

def expPublic [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (x : D.share F) (e : Nat) : Prog fs.ops D (D.share F) :=
  expBits x (bits e)

/-! ## Oblivious selection and sorting -/

/-- Select `a` for `c = 1` and `b` for `c = 0` using `b + c·(a − b)`. -/
def select [Has (Lin F) fs] [Has (Mult F) fs] (c a b : D.share F) : Prog fs.ops D (D.share F) := do
  let d ← sub a b
  let t ← mul c d
  add b t

variable [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]

/-- Compare and swap using one comparison and one multiplication.
Both outputs reuse the selected minimum: `max = a + b − min`. -/
def cswap [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b : D.share F) : Prog fs.ops D (D.share F × D.share F) := do
  let c ← lt a b
  let lo ← select c a b
  let s ← add a b
  let hi ← sub s lo
  pure (lo, hi)

/-- A four-element sorting network with three comparator layers.
Comparators within a layer are independent. -/
def sort4 [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b c d : D.share F) :
    Prog fs.ops D (D.share F × D.share F × D.share F × D.share F) := do
  let (a, b) ← cswap a b
  let (c, d) ← cswap c d
  let (a, c) ← cswap a c
  let (b, d) ← cswap b d
  let (b, c) ← cswap b c
  pure (a, b, c, d)

/-! ## Binary search with public branches -/

/-- Search a public sorted list by revealing comparison bits.
Each bit selects the next half;
for a fixed list, the resulting path is determined by the returned index. -/
def binarySearch [Has (Lin F) fs] [Has (Cmp F) fs] [Has (Reveal F) fs] [DecidableEq F]
    (s : D.share F) (xs : List F) : Prog fs.ops D Nat :=
  go xs.length xs
where
  go : Nat → List F → Prog fs.ops D Nat
    | 0, _ => pure 0
    | fuel + 1, xs =>
      if xs.length ≤ 1 then pure 0 else do
        let n := xs.length / 2
        let m ← const (xs[n]?.getD 0)
        let c ← lt s m
        let bit ← reveal c
        Prog.look bit fun bit =>        -- Wait for the comparison before choosing the next half.
          if bit = 0 then do
            let i ← go fuel (xs.drop n)
            pure (n + i)
          else
            go fuel (xs.take n)

/-! ## Randomised zero test -/

/-- Test whether `x·r` is zero for uniform `r`.
Over a finite field, zero inputs always return one;
nonzero inputs return one with probability `1 / |F|`, since `r` may be zero. -/
def isZero [Fintype F] [Inhabited F] [DecidableEq F]
    [Has (Lin F) fs] [Has (Mult F) fs] [Has (Rand F) fs] [Has (Reveal F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := do
  let r ← rand F
  let y ← mul x r
  let v ← reveal y
  const ((fun v => if v = 0 then 1 else 0) <$> v)

/-! ## Records of shares -/

structure Point (D : Domain) (F : Type) where
  x : D.share F
  y : D.share F

/-- Squared distance using two independent multiplications. -/
def dist2 [Has (Lin F) fs] [Has (Mult F) fs] (p q : Point D F) : Prog fs.ops D (D.share F) := do
  let dx ← sub p.x q.x
  let dy ← sub p.y q.y
  let sx ← mul dx dx
  let sy ← mul dy dy
  add sx sy

/-! ## Multiplication and reveal with preprocessing -/

/-- Open the two masked inputs, then open the remaining shared sum.
Adding the product of the first two openings yields `x·y`.
With precomputed triples and unit-cost reveals,
this takes two rounds and three openings. -/
def mulOpen [Fintype F] [Inhabited F] [Has (Lin F) fs] [Has (Reveal F) fs] [Has (MulTriple F) fs]
    (x y : D.share F) : Prog fs.ops D (D.clear F) := do
  let (a, b, c) ← mulTriple F
  let u₁ ← sub x a
  let e ← reveal u₁
  let u₂ ← sub y b
  let d ← reveal u₂
  let t₁ ← smul e b
  let t₂ ← smul d a
  let s ← add c t₁
  let s ← add s t₂
  let v ← reveal s
  pure (v + e * d)

/-! ## Selecting an implementation through a type class

`HasInv` prefers native inversion when available,
otherwise it computes `x^254`.
The fallback represents inversion over a field of 256 elements;
the class itself carries no correctness law.
The examples over `Rat` compare costs only. -/

/-- Select an inversion implementation; correctness is a separate obligation. -/
class HasInv (F : Type) (fs : Hybrid) (D : Domain) where
  inv : D.share F → Prog fs.ops D (D.share F)

instance (priority := high) [Inv F] [Has (Inversion F) fs] : HasInv F fs D := ⟨fun x => nativeInv x⟩
instance [OfNat F 1] [Has (Lin F) fs] [Has (Mult F) fs] : HasInv F fs D := ⟨fun x => expPublic x 254⟩

/-- Apply the selected inversion implementation, then the supplied affine program. -/
def sbox [HasInv F fs D] (affine : D.share F → Prog fs.ops D (D.share F)) (x : D.share F) : Prog fs.ops D (D.share F) := do
  let y ← HasInv.inv x
  affine y

end Programs

/-! ## Evaluation and timing checks -/

section Theorems
variable (F : Type) [Add F] [Mul F] [Sub F] [OfNat F 0] [OfNat F 1] [Inhabited F]
local notation "M" => Hybrid.eval (Std F)
local notation "T" => Std.timed F

-- Independent rows finish in the same round.
example (a b c d e f : F) :
    (Sched.output T (matVec (fs := Std F) (D := .timed) [[⟪a⟫, ⟪b⟫], [⟪c⟫, ⟪d⟫]] [⟪e⟫, ⟪f⟫])).map Timed.time
      = [1, 1] := rfl

-- Pairwise reduction has depth two for four inputs and three for eight.
example (a b c d : F) : delayOn T (prodAll (fs := Std F) (D := .timed) [⟪a⟫, ⟪b⟫, ⟪c⟫, ⟪d⟫]) = 2 := rfl
example : delayOn (Std.timed (Fin 7)) (prodAll (F := Fin 7) (fs := Std (Fin 7)) (D := .timed)
    [⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫, ⟪6⟫, ⟪0⟫, ⟪1⟫]) = 3 := by decide +kernel

-- Computing `x^5` uses two squares followed by one multiplication by `x`.
example (x : F) : delayOn T (expPublic (fs := Std F) (D := .timed) ⟪x⟫ 5) = 3 := rfl
example (x : F) : output M (expPublic (fs := Std F) (D := .ideal) x 5) = x * x * (x * x) * x := rfl

-- Squared distance has one multiplication layer and a fixed event list.
example (a b c d : F) : delayOn T (dist2 (fs := Std F) (D := .timed) ⟨⟪a⟫, ⟪b⟫⟩ ⟨⟪c⟫, ⟪d⟫⟩) = 1 := rfl
example (p q : Point .ideal F) : view M (dist2 (fs := Std F) p q)
    = [⟨Std.lin F .sub, ((), (), ()), (), ()⟩, ⟨Std.lin F .sub, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩,
       ⟨Std.lin F .add, ((), (), ()), (), ()⟩] := rfl
end Theorems

/-! ### Comparison costs -/

/-- Standard arithmetic with comparison. -/
abbrev StdCmp (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Hybrid :=
  [Lin F, Mult F, Reveal F, Cmp F]

section Cmp
variable (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]

/-- Charge `cmp` rounds and four communication units per comparison. -/
def StdCmp.timed (cmp : Nat := 3) : Model (StdCmp F).ops .timed Sched :=
  MPC.timed [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (Cmp F).priced ⟨cmp, 4⟩]
end Cmp

-- The middle outputs depend on all three comparator layers.
-- Each layer costs one comparison followed by one multiplication.
set_option maxHeartbeats 1600000 in
example : (Sched.output (StdCmp.timed Int) (sort4 (F := Int) (fs := StdCmp Int) (D := .timed) ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪2⟫)).2.1.time
    = 12 := by decide +kernel
example : (Sched.output (StdCmp.timed Int 1) (sort4 (F := Int) (fs := StdCmp Int) (D := .timed) ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪2⟫)).2.1.time
    = 6 := by decide +kernel
-- Check the sorted output on this input.
example : (output (StdCmp Int).eval (sort4 (F := Int) (fs := StdCmp Int) (D := .ideal) 3 1 4 2) : Int × Int × Int × Int)
    = (1, 2, 3, 4) := by decide +kernel

-- Search result, comparison bits and control dependencies.
section
def sorted : List Int := [1, 3, 5, 7, 9, 11, 13, 15]
example : output (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 11 sorted) = 5 := by
  decide +kernel
/-- Extract the revealed comparison bits. -/
def openedBits : List (Event (StdCmp Int).ops) → List Int :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨2, _⟩, .reveal⟩, _, out, _⟩ => some out
    | _ => none
example : openedBits (view (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 11 sorted))
    = [0, 1, 0] := by decide +kernel
example : openedBits (view (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 12 sorted))
    = [0, 1, 0] := by decide +kernel
-- Each level waits for the previous comparison bit.
-- Three levels cost `3 × (3 + 1)` rounds.
-- The returned index is plain, so its delay is the final control clock.
example : Sched.now (StdCmp.timed Int) (binarySearch (F := Int) (fs := StdCmp Int) (D := .timed) ⟪11⟫ sorted) = 12 := by
  decide +kernel
end

-- The opened value is `x·r` for uniform `r`.
-- The final constant records the result of the zero test.
section
variable (F : Type) [Field F] [Fintype F] [Inhabited F] [DecidableEq F]
abbrev ZHyb : Hybrid := [Lin F, Mult F, Reveal F, Rand F]
theorem isZero_dist (x : F) :
    dist (ZHyb F).model (isZero (fs := ZHyb F) (D := .ideal) x)
      = (uniform F).bind fun r => pure ((if x * r = 0 then 1 else 0),
          [⟨⟨3, .rand⟩, (), (), ()⟩, ⟨⟨1, .mult⟩, ((), (), ()), (), ()⟩, ⟨⟨2, .reveal⟩, ((), ()), x * r, ()⟩,
           ⟨⟨0, .const⟩, (if x * r = 0 then 1 else 0, ()), (), ()⟩]) := by
  simp only [isZero, rand, mul, reveal, const, weft]
  rfl
end

-- Two reveal rounds: the masked inputs, followed by the remaining sum.
section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]
example : delayOn (Pre.timed (Fin 7)) (mulOpen (F := Fin 7) (fs := Pre (Fin 7)) (D := .timed) ⟪3⟫ ⟪4⟫) = 2 := by
  decide +kernel
-- The triple uses independent uniform masks.
-- The view records both masked inputs and the sum before adding their product.
theorem mulOpen_dist (x y : F) :
    dist (Pre F).model (mulOpen (fs := Pre F) (D := .ideal) x y)
      = (uniform (Fin 2 → F)).bind fun v =>
          pure (x * y,
            [⟨Pre.triple F, (), ((), (), ()), ()⟩, ⟨Pre.lin F .sub, ((), (), ()), (), ()⟩, ⟨Pre.reveal F, ((), ()), x - v 0, ()⟩,
             ⟨Pre.lin F .sub, ((), (), ()), (), ()⟩, ⟨Pre.reveal F, ((), ()), y - v 1, ()⟩, ⟨Pre.lin F .smul, (x - v 0, (), ()), (), ()⟩,
             ⟨Pre.lin F .smul, (y - v 1, (), ()), (), ()⟩, ⟨Pre.lin F .add, ((), (), ()), (), ()⟩, ⟨Pre.lin F .add, ((), (), ()), (), ()⟩,
             ⟨Pre.reveal F, ((), ()), v 0 * v 1 + (x - v 0) * v 1 + (y - v 1) * v 0, ()⟩]) := by
  simp only [mulOpen, mulTriple, sub, reveal, smul, add, weft]
  congr 1
  funext v
  rw [Examples.Beaver.beaver_correct]
  rfl
end

-- Compare the exponentiation fallback with native inversion using an identity affine layer.
section
def affineId {F : Type} {fs : Hybrid} {D : Domain} : D.share F → Prog fs.ops D (D.share F) := pure
abbrev StdInv (F : Type) [Field F] : Hybrid := [Lin F, Mult F, Reveal F, Inversion F]
def StdInv.timed (F : Type) [Field F] : Model (StdInv F).ops .timed Sched :=
  MPC.timed [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (Inversion F).priced ⟨1, 2⟩]
-- Use kernel evaluation for the longer exponentiation program.
example : delayOn (Std.timed Rat) (sbox (F := Rat) (fs := Std Rat) (D := .timed) affineId ⟪3⟫) = 13 := by decide +kernel
example (x : Rat) : delayOn (StdInv.timed Rat) (sbox (fs := StdInv Rat) (D := .timed) affineId ⟪x⟫) = 1 := rfl
end

end Weft.Examples.Gallery
