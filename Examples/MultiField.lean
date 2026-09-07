import Weft
import Examples.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Programs over multiple arithmetic types

`D.share F` records the underlying type of a share.
A hybrid can offer arithmetic over several types,
with explicit functionalities for conversions and correlated randomness.

The examples use `ZMod` rings and fields.
Comparison uses canonical representatives,
and conversion maps an `Encodable` code into the target through `NatCast`.
The edaBit example omits modular correction;
the daBit example includes a Boolean-to-arithmetic realisation proof.
-/
namespace Weft.Examples.MultiField
open Weft.Examples.Basic

/-! ### Order and encoding for `ZMod n` -/

instance {n : ℕ} [NeZero n] : LT (ZMod n) := ⟨fun a b => a.val < b.val⟩
instance {n : ℕ} [NeZero n] : DecidableRel (α := ZMod n) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))
instance {n : ℕ} [NeZero n] : Encodable (ZMod n) where
  encode := ZMod.val
  decode k := some (k : ZMod n)
  encodek a := by simp

/-! ### Conversion and correlated randomness -/

namespace SwitchF
inductive Op where | switch
abbrev ops (F G : Type) : Interface where
  Op := Op
  dom _ := [.share F]
  cod _ := .share G
/-- Cast the source's `Encodable` code into the target.
For `ZMod`, use the canonical representative,
reduced modulo the target modulus. -/
def eval (F G : Type) [Encodable F] [NatCast G] : Model (ops F G) .ideal Id :=
  .silent fun ⟨.switch, (x, ())⟩ => ((Encodable.encode x : ℕ) : G)
end SwitchF

/-- Share conversion from `F` to `G`. -/
abbrev Switch (F G : Type) [Encodable F] [NatCast G] : Functionality := .ofEval (SwitchF.ops F G) (SwitchF.eval F G)

namespace EdaBitF
inductive Op where | get
abbrev ops (F : Type) (m : Nat) : Interface where
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.vec m (.share GF2))
/-- Sample uniform `r < 2^m` and return its cast in `F` with its bits. -/
noncomputable def model (F : Type) [NatCast F] (m : Nat) : Model (ops F m) .ideal PMF :=
  ⟨fun _ => (uniform (Fin (2 ^ m))).map fun r => ((((r.val : ℕ) : F), bitsOf m r.val), ())⟩
/-- Fix the mask to `coin % 2^m`. -/
def eval (F : Type) [NatCast F] (m : Nat) (coin : Nat) : Model (ops F m) .ideal Id :=
  ⟨fun _ => let r := coin % 2 ^ m; pure ((((r : ℕ) : F), bitsOf m r), ())⟩
end EdaBitF

/-- Sample `r < 2^m`, sharing its cast in `F` and its bits in `𝔽₂`.
Bits are least significant first; `coin` fixes the mask used for evaluation. -/
abbrev EdaBit (F : Type) [NatCast F] (m : Nat) (coin : Nat := 0) : Functionality :=
  ⟨EdaBitF.ops F m, EdaBitF.eval F m coin, (· = EdaBitF.model F m), Functionality.unique_eq _⟩

@[simp, weft] theorem EdaBit.model_eq (F : Type) [NatCast F] (m coin : Nat) :
    (EdaBit F m coin).model = EdaBitF.model F m := Functionality.model_eq rfl

namespace DaBitF
inductive Op where | get
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := []
  cod _ := .prod (.share F) (.share GF2)
/-- Share one uniform bit in both arithmetic types. -/
noncomputable def model (F : Type) [NatCast F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (uniform GF2).map fun (b : ZMod 2) => ((((b.val : ℕ) : F), (b : GF2)), ())⟩
def eval (F : Type) [NatCast F] (coin : Nat) : Model (ops F) .ideal Id :=
  ⟨fun _ => let b := coin % 2; pure ((((b : ℕ) : F), (b : GF2)), ())⟩
end DaBitF

/-- A daBit: one uniform bit shared in `F` and `𝔽₂`.
Used for Boolean-to-arithmetic conversion (Rotaru–Wood, ePrint 2019/207). -/
abbrev DaBit (F : Type) [NatCast F] (coin : Nat := 0) : Functionality :=
  ⟨DaBitF.ops F, DaBitF.eval F coin, (· = DaBitF.model F), Functionality.unique_eq _⟩

@[simp, weft] theorem DaBit.model_eq (F : Type) [NatCast F] (coin : Nat) :
    (DaBit F coin).model = DaBitF.model F := Functionality.model_eq rfl

section Ops
variable {fs : Hybrid} {D : Domain}
def switch {F : Type} (G : Type) [Encodable F] [NatCast G] [Has (Switch F G) fs] (a : D.share F) : Prog fs.ops D (D.share G) :=
  Prog.op (F := Switch F G) ⟨.switch, (a, ())⟩
def edabit (F : Type) [NatCast F] (m : Nat) (coin : Nat := 0) [Has (EdaBit F m coin) fs] :
    Prog fs.ops D (D.share F × (Fin m → D.share GF2)) :=
  Prog.op (F := EdaBit F m coin) ⟨.get, ()⟩
def dabit (F : Type) [NatCast F] (coin : Nat := 0) [Has (DaBit F coin) fs] : Prog fs.ops D (D.share F × D.share GF2) :=
  Prog.op (F := DaBit F coin) ⟨.get, ()⟩
end Ops

/-! ## Multiplication and comparison across types -/

section TwoFields
variable {fs : Hybrid} {D : Domain}

/-- Multiply in `F`, compare the converted result in `G`, and convert the bit back. -/
def mulThenCompare (F G : Type) [CommRing F] [Encodable F] [CommRing G] [Encodable G]
    [LT G] [DecidableRel (α := G) (· < ·)]
    [Has (Mult F) fs] [Has (Switch F G) fs] [Has (Cmp G) fs] [Has (Switch G F) fs]
    (a b c : D.share F) : Prog fs.ops D (D.share F) := do
  let ab ← mul a b                              -- Product in `F`.
  let ab' ← switch G ab                         -- Convert the product to `G`.
  let c' ← switch G c
  let bit ← lt ab' c'                           -- Comparison in `G`.
  switch F bit                                  -- Return the bit in `F`.
end TwoFields

instance : Fact (1 < 7) := ⟨by decide⟩
instance : Fact (1 < 16) := ⟨by decide⟩
instance : Fact (1 < 17) := ⟨by decide⟩

/-- Arithmetic over `𝔽₇` and `ℤ/16`, with conversion in both directions. -/
abbrev twoField : MPC := [
  (Lin (ZMod 7)).priced ⟨0, 0⟩, (Mult (ZMod 7)).priced ⟨1, 2⟩, (Reveal (ZMod 7)).priced ⟨1, 1⟩,
  (Lin (ZMod 16)).priced ⟨0, 0⟩, (Mult (ZMod 16)).priced ⟨1, 2⟩, (Cmp (ZMod 16)).priced ⟨2, 6⟩,
  (Switch (ZMod 7) (ZMod 16)).priced ⟨3, 8⟩, (Switch (ZMod 16) (ZMod 7)).priced ⟨2, 4⟩]

-- The conversion of `c` overlaps the product and its conversion.
-- The longest dependency chain costs `1 + 3 + 2 + 2 = 8` rounds.
example : commOn twoField.timed (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .timed) ⟪2⟫ ⟪3⟫ ⟪5⟫)
    = 28 := by decide +kernel
example : delayOn twoField.timed (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .timed) ⟪2⟫ ⟪3⟫ ⟪5⟫)
    = 8 := by decide +kernel
-- The product is 6 in `𝔽₇`; its representative is greater than 5 in `ℤ/16`.
example : (output twoField.eval (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .ideal) 2 3 5) : ZMod 7)
    = 0 := by decide

/-! ## Arithmetic-to-binary conversion with an edaBit -/

section A2B
variable {fs : Hybrid} {D : Domain}

/-- Ripple-carry addition of public bits to shared bits.
Each carry uses one AND; XOR and multiplication by a public bit use linear operations. -/
def addPublic [Has (Lin GF2) fs] [Has (Mult GF2) fs] :
    (m : Nat) → D.clear (Fin m → GF2) → (Fin m → D.share GF2) → D.share GF2 → Prog fs.ops D (Fin m → D.share GF2)
  | 0, _, _, _ => pure fun i => i.elim0
  | m + 1, c, r, carry => do
    let t ← add (r 0) carry                   -- r₀ ⊕ carry
    let cb ← const ((· 0) <$> c)
    let s ← add t cb                          -- s₀ = c₀ ⊕ r₀ ⊕ carry
    let rc ← mul (r 0) carry                  -- Shared AND for carry propagation.
    let ct ← smul ((· 0) <$> c) t             -- Public-bit multiplication is linear.
    let carry' ← add rc ct                    -- Carry: `maj(c₀, r₀, carry)`.
    let rest ← addPublic m (Fin.tail <$> c) (Fin.tail r) carry'
    pure (Fin.cons s rest)

/-- Open `x − r` and add its encoded low bits to the shared bits of `r`.
This example omits correction for wraparound in `F`;
the concrete check below uses a subtraction that does not wrap. -/
def a2b (F : Type) [CommRing F] [Encodable F] (m : Nat) (coin : Nat := 0)
    [Has (EdaBit F m coin) fs] [Has (Lin F) fs] [Has (Reveal F) fs] [Has (Lin GF2) fs] [Has (Mult GF2) fs]
    (x : D.share F) : Prog fs.ops D (Fin m → D.share GF2) := do
  let (r, rbits) ← edabit F m coin
  let d ← sub x r
  let c ← reveal d                             -- Disclose `x − r`.
  let zero ← const (0 : GF2)
  addPublic m ((fun c => bitsOf m (Encodable.encode c)) <$> c) rbits zero
end A2B

/-- `𝔽₁₇` and `𝔽₂` with precomputed four-bit edaBits.
The evaluation model fixes the mask to 3. -/
abbrev mixed : MPC := [
  (Lin (ZMod 17)).priced ⟨0, 0⟩, (Mult (ZMod 17)).priced ⟨1, 2⟩, (Reveal (ZMod 17)).priced ⟨1, 1⟩,
  (Lin GF2).priced ⟨0, 0⟩, (Mult GF2).priced ⟨1, 1⟩,
  (EdaBit (ZMod 17) 4 3).priced ⟨0, 0⟩]

/-- The values opened by a run over `mixed`. -/
def openedMixed : List (Event mixed.hybrid.ops) → List (ZMod 17) :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨2, _⟩, .reveal⟩, _, out, _⟩ => some out
    | _ => none

-- Evaluate the opening with mask `r = 3`.
example (x : ZMod 17) :
    openedMixed (view mixed.eval (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .ideal) x)) = [x - 3] := rfl
-- One reveal and four ANDs contribute communication.
-- The last output bit depends on three carry steps;
-- the fourth AND feeds only the unused carry-out.
example : commOn mixed.timed (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .timed) ⟪5⟫) = 5 := by
  decide +kernel
example : ((Sched.output mixed.timed (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .timed) ⟪5⟫)) 3).time = 3 := by
  decide +kernel
-- With `x = 5` and `r = 3`, subtraction does not wrap in `𝔽₁₇`.
-- The result is the four-bit representation `0101`.
example : (output mixed.eval (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .ideal) 5) : Fin 4 → ZMod 2)
    = ![1, 0, 1, 0] := by decide +kernel

/-! ## Boolean-to-arithmetic conversion with daBits

A daBit shares the same uniform bit `b` in `𝔽₂` and `F`.
Open `c = x ⊕ b`, then compute `x = c + b − 2·c·b` in `F`.
Since `c` is public, reconstruction uses only linear operations.

Independent conversions can share a reveal round.
Summing their outputs gives a Hamming weight modulo the characteristic of `F`. -/

section DaBits
variable {fs : Hybrid} {D : Domain} (F : Type) [CommRing F]

/-- Boolean → arithmetic with one daBit. -/
def b2a (coin : Nat := 0) [Has (DaBit F coin) fs] [Has (Lin GF2) fs] [Has (Reveal GF2) fs] [Has (Lin F) fs]
    (x : D.share GF2) : Prog fs.ops D (D.share F) := do
  let (bF, b₂) ← dabit F coin
  let m ← add x b₂                    -- Mask in `𝔽₂`.
  let c ← reveal m                    -- The opening is uniform.
  let cF ← const ((fun c => (c.toNat : F)) <$> c)          -- Cast the public bit into `F`.
  let s ← add cF bF                                        -- c + b
  let t ← smul ((fun c => 2 * (c.toNat : F)) <$> c) bF     -- Public coefficient `2·c`.
  sub s t                             -- x = c + b − 2cb

/-- Convert each bit and sum in `F`.
The conversions are independent; the count is represented in `F`. -/
def hammingWeight (coin : Nat := 0) [Has (DaBit F coin) fs] [Has (Lin GF2) fs] [Has (Reveal GF2) fs] [Has (Lin F) fs]
    (xs : List (D.share GF2)) : Prog fs.ops D (D.share F) := do
  let ys ← xs.mapM (b2a F coin)
  sumAll ys
end DaBits

/-- `𝔽₁₇` and `𝔽₂` with precomputed daBits.
The evaluation model fixes the shared bit to 1. -/
abbrev withDaBits : MPC := [
  (Lin (ZMod 17)).priced ⟨0, 0⟩, (Mult (ZMod 17)).priced ⟨1, 2⟩, (Reveal (ZMod 17)).priced ⟨1, 1⟩,
  (Lin GF2).priced ⟨0, 0⟩, (Reveal GF2).priced ⟨1, 1⟩,
  (DaBit (ZMod 17) 1).priced ⟨0, 0⟩]

-- Evaluate both Boolean inputs with daBit `b = 1`.
example : (output withDaBits.eval (b2a (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) 1) : ZMod 17) = 1 := by
  decide +kernel
example : (output withDaBits.eval (b2a (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) 0) : ZMod 17) = 0 := by
  decide +kernel
-- Four independent conversions give weight 3 with four openings in one round.
example : (output withDaBits.eval (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) [1, 0, 1, 1]) : ZMod 17)
    = 3 := by decide +kernel
example : commOn withDaBits.timed
    (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .timed) [⟪1⟫, ⟪0⟫, ⟪1⟫, ⟪1⟫]) = 4 := by decide +kernel
example : (Sched.output withDaBits.timed
    (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .timed) [⟪1⟫, ⟪0⟫, ⟪1⟫, ⟪1⟫])).time = 1 := by
  decide +kernel

/-! ### Boolean-to-arithmetic privacy -/

/-- Linear operations in both fields, Boolean reveal and daBits. -/
abbrev DaHyb : Hybrid := [Lin (ZMod 17), Lin GF2, Reveal GF2, DaBit (ZMod 17) 1]

/-- The view of one conversion, as a function of the opened bit. -/
def b2aView (c : GF2) : List (Event DaHyb.ops) :=
  [⟨⟨3, .get⟩, (), ((), ()), ()⟩, ⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨2, .reveal⟩, ((), ()), c, ()⟩, ⟨⟨0, .const⟩, ((c.toNat : ZMod 17), ()), (), ()⟩,
   ⟨⟨0, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .smul⟩, (2 * (c.toNat : ZMod 17), (), ()), (), ()⟩, ⟨⟨0, .sub⟩, ((), (), ()), (), ()⟩]

/-- Sample uniform `b`, open `x + b`, and reconstruct `x` in `ZMod 17`. -/
theorem b2a_dist (x : GF2) :
    dist DaHyb.model (b2a (ZMod 17) 1 (fs := DaHyb) (D := .ideal) x)
      = (uniform GF2).bind fun b => pure ((x.toNat : ZMod 17), b2aView (x + b)) := by
  -- Check reconstruction for each input bit and each mask bit.
  have out : ∀ b : GF2, ((x + b).toNat : ZMod 17) + (b.val : ZMod 17) - 2 * ((x + b).toNat : ZMod 17) * (b.val : ZMod 17)
      = (x.toNat : ZMod 17) := by
    intro b; fin_cases x <;> fin_cases b <;> decide
  simp only [b2a, b2aView, dabit, add, reveal, const, smul, sub, weft, DaBitF.model]
  congr 1
  funext b
  rw [out b]
  rfl

/-- Convert a shared Boolean to a share in `ZMod 17` without disclosure. -/
abbrev B2A : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share GF2], fun _ => .share (ZMod 17), fun _ => Unit⟩
    ⟨fun r => pure ((GF2.toNat r.args.1 : ZMod 17), ())⟩

/-- Simulate the opening with a uniform bit.
Addition by `x` permutes `𝔽₂`, so the real opening has the same distribution. -/
program b2aReal : Realization B2A DaHyb where
  impl D r := b2a (ZMod 17) 1 r.args.1
  Sim _ := (uniform GF2).map b2aView
  real r _ := by
    obtain ⟨⟨⟩, x, ⟨⟩⟩ := r
    show dist DaHyb.model (b2a (ZMod 17) 1 x) = _
    rw [b2a_dist]
    simp only [weft, Functionality.ofEval_model]
    conv_rhs => rw [← uniform_map_equiv (Equiv.addLeft x), PMF.bind_map]
    rfl

end Weft.Examples.MultiField
