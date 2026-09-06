import Weft
import Examples.Basic
import Examples.Beaver

/-!
# Gallery: what different programs look like

Each program is written once, against the functionalities it needs, and is
polymorphic in the domain and the hybrid.  The examples after each one are
what a user proves; `rfl` or `decide` means the interpreter just ran.
-/
namespace Weft.Examples.Gallery
open Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-! ## 1. Reusing programs: matrix–vector product on top of `inner` -/

/-- Every row is an inner product; rows are independent, so still one round. -/
def matVec [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 0] (rows : List (List (D.share F))) (v : List (D.share F)) :
    Prog fs.ops D (List (D.share F)) :=
  rows.mapM fun row => inner row v

/-! ## 2. Choosing the schedule: log-depth product -/

/-- Multiply adjacent pairs (independent, so one round); halves the list. -/
def pairwise [Has (Mult F) fs] : List (D.share F) → Prog fs.ops D (List (D.share F))
  | a :: b :: rest => do
    let p ← mul a b
    let ps ← pairwise rest
    pure (p :: ps)
  | xs => pure xs

/-- Product of a list by repeated pairing: `⌈log₂ n⌉` rounds, versus `n − 1`
for a fold.  The recursion is on public fuel (the length), so the program's
shape is a function of public data only. -/
def prodAll [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (xs : List (D.share F)) : Prog fs.ops D (D.share F) :=
  go xs.length xs
where
  go : Nat → List (D.share F) → Prog fs.ops D (D.share F)
    | _, [x] => pure x
    | 0, _ => const 1
    | n + 1, xs => do
      let ys ← pairwise xs
      go n ys

/-! ## 3. Public control flow: square-and-multiply with a public exponent -/

/-- The exponent is public (given as bits, least significant first), so the
*shape* of the program depends on it and the round count is a function of it. -/
def expBits [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (x : D.share F) : List Bool → Prog fs.ops D (D.share F)
  | [] => const 1
  | [b] => if b then pure x else const 1
  | b :: bs => do
    let h ← expBits x bs
    let sq ← mul h h
    if b then mul sq x else pure sq

/-- Bits of a public natural, least significant first (structural on fuel so
that it computes by `rfl`). -/
def bits (n : Nat) : List Bool := go n n
where
  go : Nat → Nat → List Bool
    | 0, _ => []
    | fuel + 1, n => if n = 0 then [] else (n % 2 = 1) :: go fuel (n / 2)

def expPublic [Has (Lin F) fs] [Has (Mult F) fs] [OfNat F 1] (x : D.share F) (e : Nat) : Prog fs.ops D (D.share F) :=
  expBits x (bits e)

/-! ## 4. Oblivious selection and a sorting network -/

/-- `if c then a else b` without branching: `b + c·(a − b)`. -/
def select [Has (Lin F) fs] [Has (Mult F) fs] (c a b : D.share F) : Prog fs.ops D (D.share F) := do
  let d ← sub a b
  let t ← mul c d
  add b t

variable [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]

/-- Compare-and-swap: one comparison, then one multiplication (both outputs
share it: `min = b + c(a − b)`, `max = a + b − min`). -/
def cswap [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b : D.share F) : Prog fs.ops D (D.share F × D.share F) := do
  let c ← lt a b
  let lo ← select c a b
  let s ← add a b
  let hi ← sub s lo
  pure (lo, hi)

/-- A 4-element sorting network: three layers; the swaps within a layer are
independent, which the timed domain sees without being told. -/
def sort4 [Has (Lin F) fs] [Has (Mult F) fs] [Has (Cmp F) fs] (a b c d : D.share F) :
    Prog fs.ops D (D.share F × D.share F × D.share F × D.share F) := do
  let (a, b) ← cswap a b
  let (c, d) ← cswap c d
  let (a, c) ← cswap a c
  let (b, d) ← cswap b d
  let (b, c) ← cswap b c
  pure (a, b, c, d)

/-! ## 5. Reactive: open, decide in the clear, continue -/

/-- Position of a secret `s` in a public sorted list, by bisection.  Each
step opens one comparison bit and branches on it in the clear.  The opened
bits are exactly the path to the answer, so the program's view is a function
of its (public) output. -/
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
        Prog.look bit fun bit =>        -- the program branches on `bit`: nothing before it is known
          if bit = 0 then do
            let i ← go fuel (xs.drop n)
            pure (n + i)
          else
            go fuel (xs.take n)

/-! ## 6. Masked opening: a zero test that reveals only the answer -/

/-- `x = 0` iff `x·r = 0` for random `r ≠ 0`.  The opened value is `x·r`:
zero when `x = 0`, uniform otherwise, so it is simulatable from the output. -/
def isZero [Fintype F] [Inhabited F] [DecidableEq F]
    [Has (Lin F) fs] [Has (Mult F) fs] [Has (Rand F) fs] [Has (Reveal F) fs] (x : D.share F) : Prog fs.ops D (D.share F) := do
  let r ← rand F
  let y ← mul x r
  let v ← reveal y
  const ((fun v => if v = 0 then 1 else 0) <$> v)

/-! ## 7. Structured data: records of shares -/

structure Point (D : Domain) (F : Type) where
  x : D.share F
  y : D.share F

/-- Squared distance between two secret points: two independent multiplications, one round. -/
def dist2 [Has (Lin F) fs] [Has (Mult F) fs] (p q : Point D F) : Prog fs.ops D (D.share F) := do
  let dx ← sub p.x q.x
  let dy ← sub p.y q.y
  let sx ← mul dx dx
  let sy ← mul dy dy
  add sx sy

/-! ## 8. Writing directly against a preprocessing functionality -/

/-- A program that *wants* a triple: multiply-and-open in one round by
opening `x − a` and `y − b`, then `x·y` is public and no extra opening is
needed.  Written against `Pre`, not `Std`. -/
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

/-! ## 9. Polymorphic over the hybrid: pick the best available implementation

An AES S-box needs a field inversion.  Some MPCs offer inversion natively;
on others it is `x^254` by square-and-multiply.  The program is written once
against a *capability class*; instance priority picks the native
functionality when the hybrid lists it and falls back otherwise.
Correctness is the same for every instance; only the cost differs, and both
are computed. -/

/-- Capability: "some way to invert".  Instances are the strategies. -/
class HasInv (F : Type) (fs : Hybrid) (D : Domain) where
  inv : D.share F → Prog fs.ops D (D.share F)

instance (priority := high) [Inv F] [Has (Inversion F) fs] : HasInv F fs D := ⟨fun x => nativeInv x⟩
instance [OfNat F 1] [Has (Lin F) fs] [Has (Mult F) fs] : HasInv F fs D := ⟨fun x => expPublic x 254⟩

/-- The S-box: inversion, then a (free) affine layer. -/
def sbox [HasInv F fs D] (affine : D.share F → Prog fs.ops D (D.share F)) (x : D.share F) : Prog fs.ops D (D.share F) := do
  let y ← HasInv.inv x
  affine y

end Programs

/-! ## The theorems, for concrete sizes -/

section Theorems
variable (F : Type) [Add F] [Mul F] [Sub F] [OfNat F 0] [OfNat F 1] [Inhabited F]
local notation "M" => Hybrid.eval (Std F)
local notation "T" => Std.timed F

-- 1. matVec: still one round (rows independent).
example (a b c d e f : F) :
    (Sched.output T (matVec (fs := Std F) (D := .timed) [[⟪a⟫, ⟪b⟫], [⟪c⟫, ⟪d⟫]] [⟪e⟫, ⟪f⟫])).map Timed.time
      = [1, 1] := rfl

-- 2. log-depth product: 4 elements, 2 rounds; 8 elements, 3 rounds.
example (a b c d : F) : delayOn T (prodAll (fs := Std F) (D := .timed) [⟪a⟫, ⟪b⟫, ⟪c⟫, ⟪d⟫]) = 2 := rfl
example : delayOn (Std.timed (Fin 7)) (prodAll (F := Fin 7) (fs := Std (Fin 7)) (D := .timed)
    [⟪1⟫, ⟪2⟫, ⟪3⟫, ⟪4⟫, ⟪5⟫, ⟪6⟫, ⟪0⟫, ⟪1⟫]) = 3 := by decide +kernel

-- 3. public exponent: x^5 = ((x²)²)·x, three multiplications in sequence.
example (x : F) : delayOn T (expPublic (fs := Std F) (D := .timed) ⟪x⟫ 5) = 3 := rfl
example (x : F) : output M (expPublic (fs := Std F) (D := .ideal) x 5) = x * x * (x * x) * x := rfl

-- 7. records: one round, silent.
example (a b c d : F) : delayOn T (dist2 (fs := Std F) (D := .timed) ⟨⟪a⟫, ⟪b⟫⟩ ⟨⟪c⟫, ⟪d⟫⟩) = 1 := rfl
example (p q : Point .ideal F) : view M (dist2 (fs := Std F) p q)
    = [⟨Std.lin F .sub, ((), (), ()), (), ()⟩, ⟨Std.lin F .sub, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩,
       ⟨Std.lin F .add, ((), (), ()), (), ()⟩] := rfl
end Theorems

/-! ### Programs that use comparison: a hybrid with `Cmp` -/

/-- The black box with comparison. -/
abbrev StdCmp (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F] : Hybrid :=
  [Lin F, Mult F, Reveal F, Cmp F]

section Cmp
variable (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableRel (α := F) (· < ·)] [Zero F] [One F]

/-- Its cost instantiation, with the comparison priced at `cmp` rounds. -/
def StdCmp.timed (cmp : Nat := 3) : Model (StdCmp F).ops .timed Sched :=
  MPC.timed [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (Cmp F).priced ⟨cmp, 4⟩]
end Cmp

-- 4. sorting network: the middle outputs go through all 3 layers, 3 × (3 + 1) rounds;
--    a cheaper comparison changes only the number.  (Closed instances over `Int`, kernel `decide`.)
set_option maxHeartbeats 1600000 in
example : (Sched.output (StdCmp.timed Int) (sort4 (F := Int) (fs := StdCmp Int) (D := .timed) ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪2⟫)).2.1.time
    = 12 := by decide +kernel
example : (Sched.output (StdCmp.timed Int 1) (sort4 (F := Int) (fs := StdCmp Int) (D := .timed) ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪2⟫)).2.1.time
    = 6 := by decide +kernel
-- ...and it sorts.
example : (output (StdCmp Int).eval (sort4 (F := Int) (fs := StdCmp Int) (D := .ideal) 3 1 4 2) : Int × Int × Int × Int)
    = (1, 2, 3, 4) := by decide +kernel

-- 5. bisection over Int: the answer, the revealed bits, and the delay.
section
def sorted : List Int := [1, 3, 5, 7, 9, 11, 13, 15]
example : output (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 11 sorted) = 5 := by
  decide +kernel
/-- The bits opened along the way: the path to the answer. -/
def openedBits : List (Event (StdCmp Int).ops) → List Int :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨2, _⟩, .reveal⟩, _, out, _⟩ => some out
    | _ => none
example : openedBits (view (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 11 sorted))
    = [0, 1, 0] := by decide +kernel
example : openedBits (view (StdCmp Int).eval (binarySearch (F := Int) (fs := StdCmp Int) (D := .ideal) 12 sorted))
    = [0, 1, 0] := by decide +kernel
-- Delay 3 × (3 + 1): each level's comparison is issued after the program has looked at the
-- previous level's opened bit.  The output is a plain index assembled from looks, so the
-- delay is `now` at the end.
example : Sched.now (StdCmp.timed Int) (binarySearch (F := Int) (fs := StdCmp Int) (D := .timed) ⟪11⟫ sorted) = 12 := by
  decide +kernel
end

-- 6. zero test: the semantics.  What is revealed is `x · r` for a fresh uniform
--    `r`, and nothing else; the output is a function of it.
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

-- 8. multiply-and-reveal on the preprocessing functionality: two rounds, three reveals.
section
variable (F : Type) [Field F] [Fintype F] [Inhabited F]
example : delayOn (Pre.timed (Fin 7)) (mulOpen (F := Fin 7) (fs := Pre (Fin 7)) (D := .timed) ⟪3⟫ ⟪4⟫) = 2 := by
  decide +kernel
-- The semantics: the triple is a jointly uniform pair, and the three opened
-- values are the two masked inputs and the masked product.
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

-- 9. capability dispatch: same S-box source, 13 rounds on the black box, 1 round with native inversion.
section
def affineId {F : Type} {fs : Hybrid} {D : Domain} : D.share F → Prog fs.ops D (D.share F) := pure
abbrev StdInv (F : Type) [Field F] : Hybrid := [Lin F, Mult F, Reveal F, Inversion F]
def StdInv.timed (F : Type) [Field F] : Model (StdInv F).ops .timed Sched :=
  MPC.timed [(Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩, (Inversion F).priced ⟨1, 2⟩]
-- (closed instance with kernel `decide`; the elaborator's `whnf` is slow at this depth)
example : delayOn (Std.timed Rat) (sbox (F := Rat) (fs := Std Rat) (D := .timed) affineId ⟪3⟫) = 13 := by decide +kernel
example (x : Rat) : delayOn (StdInv.timed Rat) (sbox (fs := StdInv Rat) (D := .timed) affineId ⟪x⟫) = 1 := rfl
end

end Weft.Examples.Gallery
