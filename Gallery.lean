import Glean

/-!
# Gallery: what different circuits look like

Each circuit is written once, against the features it needs, and is
polymorphic in the domain `D` and the signature `σ`.  The examples after
each one are what a user proves; `rfl` means the interpreter just ran.
-/
namespace Glean.Gallery
open Glean Glean.Examples

variable {D : Domain} {σ : Sig}

/-! ## 1. Reusing gadgets: matrix–vector product on top of `inner` -/

/-- Every row is an inner product; rows are independent, so still one round. -/
def matVec [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 0]
    (rows : List (List D.S)) (v : List D.S) : Circ σ (List D.S) :=
  rows.mapM fun row => inner row v

/-! ## 2. Choosing the schedule: log-depth product -/

/-- Multiply adjacent pairs (independent, so one round); halves the list. -/
def pairwise [Has (Mult D) σ] : List D.S → Circ σ (List D.S)
  | a :: b :: rest => do
    let p ← mul a b
    let ps ← pairwise rest
    pure (p :: ps)
  | xs => pure xs

/-- Product of a list by repeated pairing: `⌈log₂ n⌉` delay, versus `n - 1`
for a fold.  The recursion is on public fuel (the length), so the circuit's
shape is a function of public data only. -/
def prodAll [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 1] (xs : List D.S) : Circ σ D.S :=
  go xs.length xs
where
  go : Nat → List D.S → Circ σ D.S
    | _, [x] => pure x
    | 0, _ => const (1 : D.F)
    | n + 1, xs => do
      let ys ← pairwise xs
      go n ys

/-! ## 3. Public control flow: square-and-multiply with a public exponent -/

/-- The exponent is public (given as bits, least significant first), so the
*shape* of the circuit depends on it and the round count is a function of it. -/
def expBits [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 1] (x : D.S) : List Bool → Circ σ D.S
  | [] => const (1 : D.F)
  | [b] => if b then pure x else const (1 : D.F)
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

def expPublic [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 1] (x : D.S) (e : Nat) : Circ σ D.S :=
  expBits x (bits e)

/-! ## 4. Oblivious selection and a sorting network -/

/-- `if c then a else b` without branching: `b + c·(a - b)`. -/
def select [Has (Lin D) σ] [Has (Mult D) σ] (c a b : D.S) : Circ σ D.S := do
  let d ← sub a b
  let t ← mul c d
  add b t

/-- Compare-and-swap: one comparison, then one multiplication (both branches
share it: `min = b + c(a-b)`, `max = a + b - min`). -/
def cswap [Has (Lin D) σ] [Has (Mult D) σ] [Has (Cmp D) σ] (a b : D.S) : Circ σ (D.S × D.S) := do
  let c ← lt a b
  let lo ← select c a b
  let s ← add a b
  let hi ← sub s lo
  pure (lo, hi)

/-- A 4-element sorting network: three layers; the swaps within a layer are
independent, which the timed domain sees without being told. -/
def sort4 [Has (Lin D) σ] [Has (Mult D) σ] [Has (Cmp D) σ]
    (a b c d : D.S) : Circ σ (D.S × D.S × D.S × D.S) := do
  let (a, b) ← cswap a b
  let (c, d) ← cswap c d
  let (a, c) ← cswap a c
  let (b, d) ← cswap b d
  let (b, c) ← cswap b c
  pure (a, b, c, d)

/-! ## 5. Reactive: open, decide in the clear, continue -/

/-- Position of a secret `s` in a public sorted list, by bisection.  Each
step opens one comparison bit and branches on it in the clear.  The opened
bits are exactly the path to the answer, so the circuit is hiding: its
leakage is a function of its (public) output. -/
def binarySearch [Has (Lin D) σ] [Has (Cmp D) σ] [Has (Reveal D) σ] [Has (Barrier D) σ]
    [OfNat D.F 0] [DecidableEq D.F]
    (s : D.S) (xs : List D.F) : Circ σ Nat :=
  go xs.length xs
where
  go : Nat → List D.F → Circ σ Nat
    | 0, _ => pure 0
    | fuel + 1, xs =>
      if xs.length ≤ 1 then pure 0 else do
        let n := xs.length / 2
        let m ← const (xs[n]?.getD 0)
        let c ← lt s m
        let bit ← reveal c
        barrier D                       -- the circuit is about to branch on `bit`
        if bit = 0 then do
          let i ← go fuel (xs.drop n)
          pure (n + i)
        else
          go fuel (xs.take n)

/-! ## 6. Masked opening: a zero test that reveals only the answer -/

/-- `x = 0` iff `x·r = 0` for random `r ≠ 0`.  The opened value is `x·r`:
zero when `x = 0`, uniform otherwise, so it is simulatable from the output. -/
def isZero [Has (Lin D) σ] [Has (Mult D) σ] [Has (Rand D) σ] [Has (Reveal D) σ]
    [DecidableEq D.F] [OfNat D.F 0] [OfNat D.F 1] (x : D.S) : Circ σ D.S := do
  let r ← rand
  let y ← mul x r
  let v ← reveal y
  const (if v = 0 then (1 : D.F) else 0)

/-! ## 7. Structured data: records of shares -/

structure Point (D : Domain) where
  x : D.S
  y : D.S

/-- Squared distance between two secret points: two independent mults, one round. -/
def dist2 [Has (Lin D) σ] [Has (Mult D) σ] (p q : Point D) : Circ σ D.S := do
  let dx ← sub p.x q.x
  let dy ← sub p.y q.y
  let sx ← mul dx dx
  let sy ← mul dy dy
  add sx sy

/-! ## 8. Writing directly against a preprocessing functionality -/

/-- A circuit that *wants* a triple: multiply-and-open in one round by
opening `x - a` and `y - b`, then `x·y` is public and no extra opening is
needed.  Written against `Pre`, not `Std`. -/
def mulOpen [Has (Lin D) σ] [Has (Reveal D) σ] [Has (MulTriple D) σ] [Mul D.F] [Add D.F]
    (x y : D.S) : Circ σ D.F := do
  let (a, b, c) ← mulTriple
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

/-! ## 9. Polymorphic over the feature set: pick the best available implementation

An AES S-box needs a field inversion.  Some MPCs offer inversion natively;
on others it is `x^254` by square-and-multiply.  The circuit is written once
against a *capability class*; instance priority picks the native feature
when the signature has it and falls back otherwise.  Correctness is the
same for every instance; only the cost differs, and both are computed. -/

/-- A native inversion sub-functionality. -/
inductive Inv (D : Domain) : Sig where
  | inv : D.S → Inv D D.S

/-- Capability: "some way to invert".  Instances are the strategies. -/
class HasInv (D : Domain) (σ : Sig) where
  inv : D.S → Circ σ D.S

instance (priority := high) [Has (Inv D) σ] : HasInv D σ := ⟨fun x => Circ.op (Inv.inv x)⟩
instance [Has (Lin D) σ] [Has (Mult D) σ] [OfNat D.F 1] : HasInv D σ := ⟨fun x => expPublic x 254⟩

/-- The S-box: inversion, then a (free) affine layer. -/
def sbox [HasInv D σ] [Has (Lin D) σ] (affine : D.S → Circ σ D.S) (x : D.S) : Circ σ D.S := do
  let y ← HasInv.inv x
  affine y

/-! ## 10. The same idea with a cost function instead of the type system

Alternatively write against the *union* of features and let a cost function
price unsupported operations at `⊤`.  "Runs on this MPC" becomes "has finite
cost", and a circuit family can choose its implementation by comparing
prices.  This keeps one signature and moves feature availability into data. -/

abbrev StdInv (D : Domain) : Sig := Std D ⊞ Inv D

/-- Multiplications, as an additive cost. -/
def Std.mults {D : Domain} : {α : Type} → Std D α → WithTop ℕ
  | _, .inr (.inl _) => 1
  | _, _ => 0
/-- Cost (in multiplications) on an MPC *without* native inversion: `inv` is unsupported. -/
def noInv {D : Domain} : CostModel (StdInv D) (WithTop ℕ) :=
  ⟨fun o => match o with | .inl o => Std.mults o | .inr _ => ⊤⟩
/-- ...and on an MPC *with* native inversion, priced as one multiplication. -/
def withInv {D : Domain} : CostModel (StdInv D) (WithTop ℕ) :=
  ⟨fun o => match o with | .inl o => Std.mults o | .inr _ => 1⟩

/-- Choose by price: native inversion if it is cheaper than the exponentiation route. -/
def invBest [OfNat D.F 1] (K : CostModel (StdInv D) (WithTop ℕ)) (x : D.S) : Circ (StdInv D) D.S :=
  if K.op (Has.inj (Inv.inv x)) ≤ (13 : WithTop ℕ) then Circ.op (Inv.inv x) else expPublic x 254

/-! ## The theorems, for concrete sizes -/

section
variable (F : Type) [Add F] [Mul F] [Sub F] [OfNat F 0] [OfNat F 1] [Inhabited F]
local notation "𝕀" => Domain.ideal F
local notation "𝕋" => Domain.timed F
local notation "⟪" x "⟫" => (⟨x, 0⟩ : Timed F)
local notation "M" => Std.ideal F
local notation "T" => Std.timed F

-- 1. matVec: still one round (rows independent), reuses inner's proof shape.
example (a b c d e f : F) :
    (Sched.output T (matVec (D := 𝕋) (σ := Std 𝕋) [[⟪a⟫, ⟪b⟫], [⟪c⟫, ⟪d⟫]] [⟪e⟫, ⟪f⟫])).map Timed.time
      = [1, 1] := rfl

-- 2. log-depth product: 4 elements, 2 rounds; 8 elements, 3 rounds.
example (a b c d : F) :
    delay F T (prodAll (D := 𝕋) (σ := Std 𝕋) [⟪a⟫, ⟪b⟫, ⟪c⟫, ⟪d⟫]) = 2 := rfl
example (a b c d e f g h : F) :
    delay F T (prodAll (D := 𝕋) (σ := Std 𝕋) [⟪a⟫, ⟪b⟫, ⟪c⟫, ⟪d⟫, ⟪e⟫, ⟪f⟫, ⟪g⟫, ⟪h⟫]) = 3 := rfl

-- 3. public exponent: x^5 = ((x²)²)·x, three multiplications in sequence.
example (x : F) : delay F T (expPublic (D := 𝕋) (σ := Std 𝕋) ⟪x⟫ 5) = 3 := rfl
example (x : F) : output M (expPublic (D := 𝕀) (σ := Std 𝕀) x 5) = x * x * (x * x) * x := rfl

-- 9. feature dispatch: same S-box source, 13 rounds on Std, 1 round with native inversion.
def affineId : D.S → Circ σ D.S := pure
def Inv.timed (ℓ : Nat) : Model (Inv 𝕋) F Sched where
  program o := match o with | .inv x => Timed.after [x.time] ℓ x.val
  leak _ _ := []
-- (closed instance with kernel `decide`; the elaborator's `whnf` is slow at this depth)
example : delay Int (Std.timed Int) (sbox (D := .timed Int) (σ := Std _) affineId ⟨3, 0⟩) = 13 := by
  decide
example (x : F) :
    delayOn ((Std.timed F).sum (Inv.timed F 1)) (sbox (D := 𝕋) (σ := StdInv 𝕋) affineId ⟪x⟫) = 1 := rfl

-- 10. cost functions with ⊤: the native op is infinitely expensive on `noInv`,
--     and `invBest` picks the finite route.
def StdInv.ideal : Model (StdInv 𝕀) F Id := (Std.ideal F).sum ⟨fun o => match o with | .inv x => pure x, fun _ _ => []⟩
example (x : F) : cost (StdInv.ideal F) noInv (Circ.op (Inv.inv (D := 𝕀) x) : Circ (StdInv 𝕀) _) = ⊤ := rfl
example (x : F) : cost (StdInv.ideal F) noInv (invBest noInv x) = 13 := rfl
example (x : F) : cost (StdInv.ideal F) withInv (invBest withInv x) = 1 := rfl

-- 7. records: one round, silent.
example (a b c d : F) : delay F T (dist2 (D := 𝕋) (σ := Std 𝕋) ⟨⟪a⟫, ⟪b⟫⟩ ⟨⟪c⟫, ⟪d⟫⟩) = 1 := rfl
example (p q : Point 𝕀) : leak M (dist2 (σ := Std 𝕀) p q) = [] := rfl
end

/-! ### Circuits that use comparison: a signature with `Cmp` and `Barrier` -/

abbrev StdCmp (D : Domain) : Sig := Std D ⊞ Cmp D ⊞ Barrier D

section
variable (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1] [Inhabited F]
local notation "𝕀" => Domain.ideal F
local notation "𝕋" => Domain.timed F
local notation "⟪" x "⟫" => (⟨x, 0⟩ : Timed F)

def Cmp.ideal {L} : Model (Cmp 𝕀) L Id where
  program o := match o with | .lt a b => pure (if a < b then 1 else 0)
  leak _ _ := []
def Cmp.timed (ℓ : Nat) : Model (Cmp 𝕋) F Sched where
  program o := match o with | .lt a b => Timed.after [a.time, b.time] ℓ (if a.val < b.val then 1 else 0)
  leak _ _ := []

def StdCmp.ideal : Model (StdCmp 𝕀) F Id := (Std.ideal F).sum ((Cmp.ideal F).sum (Barrier.ideal F))
/-- Timed, with the comparison priced at `cmp` rounds. -/
def StdCmp.timed (cmp : Nat := 3) : Model (StdCmp 𝕋) F Sched :=
  (Std.timed F).sum ((Cmp.timed F cmp).sum (Barrier.timed F))

end

-- 4. sorting network: the middle outputs go through all 3 layers, 3 × (3 + 1) rounds;
--    a cheaper comparison changes only the number.  (Closed instances over `Int`, kernel `decide`.)
example : (Sched.output (StdCmp.timed Int) (sort4 (D := .timed Int) (σ := StdCmp _) ⟨3, 0⟩ ⟨1, 0⟩ ⟨4, 0⟩ ⟨2, 0⟩)).2.1.time = 12 := by
  decide
example : (Sched.output (StdCmp.timed Int 1) (sort4 (D := .timed Int) (σ := StdCmp _) ⟨3, 0⟩ ⟨1, 0⟩ ⟨4, 0⟩ ⟨2, 0⟩)).2.1.time = 6 := by
  decide
-- ...and it sorts.
example : ((output (StdCmp.ideal Int) (sort4 (D := .ideal Int) (σ := StdCmp _) 3 1 4 2)) : Int × Int × Int × Int) = (1, 2, 3, 4) := by
  decide

-- 5. bisection over Int: the answer, the revealed bits, and the delay.
section
local notation "𝕀" => Domain.ideal Int
local notation "𝕋" => Domain.timed Int
local notation "M" => StdCmp.ideal Int
def sorted : List Int := [1, 3, 5, 7, 9, 11, 13, 15]
example : output M (binarySearch (D := 𝕀) (σ := StdCmp 𝕀) 11 sorted) = 5 := rfl
example : leak M (binarySearch (D := 𝕀) (σ := StdCmp 𝕀) 11 sorted) = [0, 1, 0] := rfl
example : leak M (binarySearch (D := 𝕀) (σ := StdCmp 𝕀) 12 sorted) = [0, 1, 0] := rfl
-- Delay 3 × (3 + 1): each level's comparison waits, through the barrier, for the
-- previous level's revealed bit.  Without the barrier the levels would look
-- independent and the count would be 4.
example : delayClear (StdCmp.timed Int) (binarySearch (D := 𝕋) (σ := StdCmp 𝕋) ⟨11, 0⟩ sorted) = 12 := by
  decide
end

-- 6. zero test: the semantics.  What is revealed is `x · r` for a fresh uniform
--    `r`, and nothing else; the output is a function of it.
section
variable (F : Type) [Field F] [Fintype F] [DecidableEq F]
abbrev ZSig (D : Domain) : Sig := Std D ⊞ Rand D
noncomputable def Z.ideal : Model (ZSig (.ideal F)) F PMF := ((Std.ideal F).lift PMF).sum (Rand.ideal F)
theorem isZero_dist (x : F) :
    dist (Z.ideal F) (isZero (D := .ideal F) (σ := ZSig _) x)
      = (uniform F).bind fun r => pure ((if x * r = 0 then 1 else 0), [x * r]) := by
  simp [dist, isZero, Z.ideal, Model.sum, Lin.ideal, Mult.ideal, Reveal.ideal, Rand.ideal, Std.ideal,
    rand, mul, reveal, const, Circ.op, Has.inj, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map]
end

-- 8. multiply-and-reveal on the preprocessing functionality: two rounds, three reveals.
section
variable (F : Type) [Field F] [Fintype F]
local notation "𝕀" => Domain.ideal F
example : delayClear (Pre.timed Int 1 0) (mulOpen (D := .timed Int) (σ := Pre _) ⟨3, 0⟩ ⟨4, 0⟩) = 2 := by
  decide
-- The semantics: the triple is a jointly uniform pair, and the three opened
-- values are the two masked inputs and the masked product.
theorem mulOpen_dist (x y : F) :
    dist (Pre.ideal F) (mulOpen (D := 𝕀) (σ := Pre 𝕀) x y)
      = (uniform (Fin 2 → F)).bind fun v =>
          pure (x * y, [x - v 0, y - v 1, v 0 * v 1 + (x - v 0) * v 1 + (y - v 1) * v 0]) := by
  simp [dist, mulOpen, Pre.ideal, Model.sum, Lin.ideal, Reveal.ideal, MulTriple.ideal, 
    Correlation.sample, MulTriple.corr, sub, reveal, smul, add, mulTriple, Circ.op, Has.inj, run,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map,
    PMF.bind_map, Function.comp_def]
  congr 1
  funext v
  rw [beaver_correct]
end

end Glean.Gallery
