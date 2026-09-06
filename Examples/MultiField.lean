import Weft
import Examples.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Generic over the field: shares as a type constructor

Shares are a type constructor: `D.share F` is "a share of an `F`".  Every
functionality is instantiated at a concrete field, a hybrid lists the
fields it offers each on, and switching between two fields is one more
functionality.  A program is generic over the fields it touches; which
field a value lives in is in its type, so a mismatch is a type error.

What the models need of a field, all from Mathlib: `CommRing F` for the
arithmetic, an order for `cmp` (on `ZMod n`, of canonical representatives),
and `Encodable F` for the conversions, which go through the canonical
representative.
-/
namespace Weft.Examples.MultiField
open Weft.Examples.Basic

/-! ### `ZMod n` as a concrete field: order and encoding by canonical representative -/

instance {n : ℕ} [NeZero n] : LT (ZMod n) := ⟨fun a b => a.val < b.val⟩
instance {n : ℕ} [NeZero n] : DecidableRel (α := ZMod n) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))
instance {n : ℕ} [NeZero n] : Encodable (ZMod n) where
  encode := ZMod.val
  decode k := some (k : ZMod n)
  encodek a := by simp

/-! ### Switching, edaBits, daBits: functionalities across two fields -/

namespace SwitchF
inductive Op where | switch
abbrev ops (F G : Type) : Interface where
  Op := Op
  dom _ := [.share F]
  cod _ := .share G
/-- The canonical representative, re-read in the target (the integer value if in range). -/
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
/-- A uniform `r < 2^m`, together with its bits. -/
noncomputable def model (F : Type) [NatCast F] (m : Nat) : Model (ops F m) .ideal PMF :=
  ⟨fun _ => (uniform (Fin (2 ^ m))).map fun r => ((((r.val : ℕ) : F), bitsOf m r.val), ())⟩
/-- With the mask fixed to `coin`. -/
def eval (F : Type) [NatCast F] (m : Nat) (coin : Nat) : Model (ops F m) .ideal Id :=
  ⟨fun _ => let r := coin % 2 ^ m; pure ((((r : ℕ) : F), bitsOf m r), ())⟩
end EdaBitF

/-- An edaBit: a random `r < 2^m` shared over `F`, together with its `m` bits
shared over `𝔽₂` (least significant first).  A correlation across two
fields.  `coin` fixes the mask under the evaluation model. -/
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
/-- One uniform bit, seen in both fields. -/
noncomputable def model (F : Type) [NatCast F] : Model (ops F) .ideal PMF :=
  ⟨fun _ => (uniform GF2).map fun (b : ZMod 2) => ((((b.val : ℕ) : F), (b : GF2)), ())⟩
def eval (F : Type) [NatCast F] (coin : Nat) : Model (ops F) .ideal Id :=
  ⟨fun _ => let b := coin % 2; pure ((((b : ℕ) : F), (b : GF2)), ())⟩
end DaBitF

/-- A daBit (Rotaru–Wood, ePrint 2019/207): one uniformly random bit `b`,
shared over `F` *and* over `𝔽₂`.  The simplest correlation across two
fields, and the one behind Boolean ↔ arithmetic conversion. -/
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

/-! ## Example: generic over two fields, comparison offered on the second -/

section TwoFields
variable {fs : Hybrid} {D : Domain}

/-- Multiply in `F`, switch to `G` where comparison is offered, compare, switch back. -/
def mulThenCompare (F G : Type) [CommRing F] [Encodable F] [CommRing G] [Encodable G]
    [LT G] [DecidableRel (α := G) (· < ·)]
    [Has (Mult F) fs] [Has (Switch F G) fs] [Has (Cmp G) fs] [Has (Switch G F) fs]
    (a b c : D.share F) : Prog fs.ops D (D.share F) := do
  let ab ← mul a b                              -- in F
  let ab' ← switch G ab                         -- conversions: independent, so one round
  let c' ← switch G c
  let bit ← lt ab' c'                           -- comparison is offered on G
  switch F bit                                  -- back in F
end TwoFields

instance : Fact (1 < 7) := ⟨by decide⟩
instance : Fact (1 < 16) := ⟨by decide⟩
instance : Fact (1 < 17) := ⟨by decide⟩

/-- An MPC over `𝔽₇` and `ℤ/16`. -/
abbrev twoField : MPC := [
  (Lin (ZMod 7)).priced ⟨0, 0⟩, (Mult (ZMod 7)).priced ⟨1, 2⟩, (Reveal (ZMod 7)).priced ⟨1, 1⟩,
  (Lin (ZMod 16)).priced ⟨0, 0⟩, (Mult (ZMod 16)).priced ⟨1, 2⟩, (Cmp (ZMod 16)).priced ⟨2, 6⟩,
  (Switch (ZMod 7) (ZMod 16)).priced ⟨3, 8⟩, (Switch (ZMod 16) (ZMod 7)).priced ⟨2, 4⟩]

-- Nothing is revealed (every event is silent); communication adds; delay is the critical path:
-- the switch of `c` overlaps the multiplication and the switch of `ab` (1 + 3 + 2 + 2 = 8).
example : commOn twoField.timed (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .timed) ⟪2⟫ ⟪3⟫ ⟪5⟫)
    = 28 := by decide +kernel
example : delayOn twoField.timed (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .timed) ⟪2⟫ ⟪3⟫ ⟪5⟫)
    = 8 := by decide +kernel
-- 2·3 = 6 in 𝔽₇, compared with 5 in ℤ/16: not less, so 0.
example : (output twoField.eval (mulThenCompare (ZMod 7) (ZMod 16) (fs := twoField.hybrid) (D := .ideal) 2 3 5) : ZMod 7)
    = 0 := by decide

/-! ## Example: arithmetic → binary conversion with an edaBit -/

section A2B
variable {fs : Hybrid} {D : Domain}

/-- Ripple-carry addition of a *public* `c` (as bits) to shared bits, over
`𝔽₂` shares: xor is free (`Lin`), and is a round (`Mult`).  `m` rounds. -/
def addPublic [Has (Lin GF2) fs] [Has (Mult GF2) fs] :
    (m : Nat) → D.clear (Fin m → GF2) → (Fin m → D.share GF2) → D.share GF2 → Prog fs.ops D (Fin m → D.share GF2)
  | 0, _, _, _ => pure fun i => i.elim0
  | m + 1, c, r, carry => do
    let t ← add (r 0) carry                   -- r₀ ⊕ carry
    let cb ← const ((· 0) <$> c)
    let s ← add t cb                          -- s₀ = c₀ ⊕ r₀ ⊕ carry
    let rc ← mul (r 0) carry                  -- r₀ ∧ carry          (the one round)
    let ct ← smul ((· 0) <$> c) t             -- c₀ ∧ (r₀ ⊕ carry)   (public bit: free)
    let carry' ← add rc ct                    -- maj(c₀, r₀, carry), branch-free
    let rest ← addPublic m (Fin.tail <$> c) (Fin.tail r) carry'
    pure (Fin.cons s rest)

/-- A2B: reveal `x − r`, then `x = (x − r) + r` bit by bit, with `r`'s bits
already shared over `𝔽₂`.  One reveal round, then `m` rounds of the adder. -/
def a2b (F : Type) [CommRing F] [Encodable F] (m : Nat) (coin : Nat := 0)
    [Has (EdaBit F m coin) fs] [Has (Lin F) fs] [Has (Reveal F) fs] [Has (Lin GF2) fs] [Has (Mult GF2) fs]
    (x : D.share F) : Prog fs.ops D (Fin m → D.share GF2) := do
  let (r, rbits) ← edabit F m coin
  let d ← sub x r
  let c ← reveal d                             -- the only revealed value: x − r
  let zero ← const (0 : GF2)
  addPublic m ((fun c => bitsOf m (Encodable.encode c)) <$> c) rbits zero
end A2B

/-- A mixed `𝔽₁₇` / `𝔽₂` MPC with 4-bit edaBits from preprocessing, the mask fixed to `3`
under evaluation. -/
abbrev mixed : MPC := [
  (Lin (ZMod 17)).priced ⟨0, 0⟩, (Mult (ZMod 17)).priced ⟨1, 2⟩, (Reveal (ZMod 17)).priced ⟨1, 1⟩,
  (Lin GF2).priced ⟨0, 0⟩, (Mult GF2).priced ⟨1, 1⟩,
  (EdaBit (ZMod 17) 4 3).priced ⟨0, 0⟩]

/-- The values opened by a run over `mixed`. -/
def openedMixed : List (Event mixed.hybrid.ops) → List (ZMod 17) :=
  List.filterMap fun e => match e with
    | ⟨⟨⟨2, _⟩, .reveal⟩, _, out, _⟩ => some out
    | _ => none

-- What is revealed: `x − r`, as its representative (evaluation with the mask `r = 3`).
example (x : ZMod 17) :
    openedMixed (view mixed.eval (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .ideal) x)) = [x - 3] := rfl
-- Communication: one reveal and four ANDs.  Delay of the last bit: the carry chain starts
-- from a program-time zero at round 0 and the opened bits arrive at round 1, so three
-- carries (the fourth AND only feeds the unused carry-out): 3.
example : commOn mixed.timed (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .timed) ⟪5⟫) = 5 := by
  decide +kernel
example : ((Sched.output mixed.timed (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .timed) ⟪5⟫)) 3).time = 3 := by
  decide +kernel
-- Correctness on instances: the bits of 5 = 0b0101, under the mask 3.  (This simplified A2B
-- omits the modular correction of the real edaBit protocol, so it is correct under `r ≤ x`.)
example : (output mixed.eval (a2b (ZMod 17) 4 3 (fs := mixed.hybrid) (D := .ideal) 5) : Fin 4 → ZMod 2)
    = ![1, 0, 1, 0] := by decide +kernel

/-! ## Example: daBits, and a program that spans two fields

A daBit is a bit `b` shared in both worlds.  With one daBit, a Boolean
share `⟦x⟧₂` becomes an arithmetic share `⟦x⟧_F` at the cost of one
reveal: open `c = x ⊕ b` in `𝔽₂` (a uniform bit, so it says nothing about
`x`), then `x = c + b − 2·c·b` in `F`, which is linear in `⟦b⟧_F` once `c`
is public.  Chained through a list, the conversions are independent (one
reveal round in total), and the sum in `F` is free. -/

section DaBits
variable {fs : Hybrid} {D : Domain} (F : Type) [CommRing F]

/-- Boolean → arithmetic with one daBit. -/
def b2a (coin : Nat := 0) [Has (DaBit F coin) fs] [Has (Lin GF2) fs] [Has (Reveal GF2) fs] [Has (Lin F) fs]
    (x : D.share GF2) : Prog fs.ops D (D.share F) := do
  let (bF, b₂) ← dabit F coin
  let m ← add x b₂                    -- x ⊕ b, over 𝔽₂
  let c ← reveal m                    -- the one revealed value: a uniform bit
  let cF ← const ((fun c => (c.toNat : F)) <$> c)          -- c, as an element of F
  let s ← add cF bF                                        -- c + b
  let t ← smul ((fun c => 2 * (c.toNat : F)) <$> c) bF     -- 2·c·b, linear: c is public
  sub s t                             -- x = c + b − 2cb

/-- Hamming weight: bits in, arithmetic share out.  All conversions in one
round, then a free sum. -/
def hammingWeight (coin : Nat := 0) [Has (DaBit F coin) fs] [Has (Lin GF2) fs] [Has (Reveal GF2) fs] [Has (Lin F) fs]
    (xs : List (D.share GF2)) : Prog fs.ops D (D.share F) := do
  let ys ← xs.mapM (b2a F coin)
  sumAll ys
end DaBits

/-- An MPC over `𝔽₁₇` and `𝔽₂` with daBits from preprocessing (the bit fixed to `1` under evaluation). -/
abbrev withDaBits : MPC := [
  (Lin (ZMod 17)).priced ⟨0, 0⟩, (Mult (ZMod 17)).priced ⟨1, 2⟩, (Reveal (ZMod 17)).priced ⟨1, 1⟩,
  (Lin GF2).priced ⟨0, 0⟩, (Reveal GF2).priced ⟨1, 1⟩,
  (DaBit (ZMod 17) 1).priced ⟨0, 0⟩]

-- Correctness on instances, for the daBit `b = 1`.
example : (output withDaBits.eval (b2a (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) 1) : ZMod 17) = 1 := by
  decide +kernel
example : (output withDaBits.eval (b2a (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) 0) : ZMod 17) = 0 := by
  decide +kernel
-- The Hamming weight of `1, 0, 1, 1` is 3, in 𝔽₁₇; four reveals; one round, not four.
example : (output withDaBits.eval (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .ideal) [1, 0, 1, 1]) : ZMod 17)
    = 3 := by decide +kernel
example : commOn withDaBits.timed
    (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .timed) [⟪1⟫, ⟪0⟫, ⟪1⟫, ⟪1⟫]) = 4 := by decide +kernel
example : (Sched.output withDaBits.timed
    (hammingWeight (ZMod 17) 1 (fs := withDaBits.hybrid) (D := .timed) [⟪1⟫, ⟪0⟫, ⟪1⟫, ⟪1⟫])).time = 1 := by
  decide +kernel

/-! ### Privacy of `b2a`: the revealed bit is uniform for either input -/

/-- The daBit hybrid, unpriced. -/
abbrev DaHyb : Hybrid := [Lin (ZMod 17), Lin GF2, Reveal GF2, DaBit (ZMod 17) 1]

/-- The view of one conversion, as a function of the opened bit. -/
def b2aView (c : GF2) : List (Event DaHyb.ops) :=
  [⟨⟨3, .get⟩, (), ((), ()), ()⟩, ⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨2, .reveal⟩, ((), ()), c, ()⟩, ⟨⟨0, .const⟩, ((c.toNat : ZMod 17), ()), (), ()⟩,
   ⟨⟨0, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .smul⟩, (2 * (c.toNat : ZMod 17), (), ()), (), ()⟩, ⟨⟨0, .sub⟩, ((), (), ()), (), ()⟩]

/-- **The semantics of `b2a`**: draw a uniform bit `b`, reveal `x + b`, output `x` in `F`. -/
theorem b2a_dist (x : GF2) :
    dist DaHyb.model (b2a (ZMod 17) 1 (fs := DaHyb) (D := .ideal) x)
      = (uniform GF2).bind fun b => pure ((x.toNat : ZMod 17), b2aView (x + b)) := by
  -- correctness of the reconstruction, for both values of `x` and of the daBit
  have out : ∀ b : GF2, ((x + b).toNat : ZMod 17) + (b.val : ZMod 17) - 2 * ((x + b).toNat : ZMod 17) * (b.val : ZMod 17)
      = (x.toNat : ZMod 17) := by
    intro b; fin_cases x <;> fin_cases b <;> decide
  simp only [b2a, b2aView, dabit, add, reveal, const, smul, sub, weft, DaBitF.model]
  congr 1
  funext b
  rw [out b]
  rfl

/-- The Boolean-to-arithmetic functionality: one `𝔽₂` operand, a share of `F`, nothing declared. -/
abbrev B2A : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share GF2], fun _ => .share (ZMod 17), fun _ => Unit⟩
    ⟨fun r => pure ((GF2.toNat r.args.1 : ZMod 17), ())⟩

/-- **Privacy.**  The revealed bit `x + b` is uniform for either `x`: `b ↦ x + b`
is a bijection of `𝔽₂`; the simulator flips a coin. -/
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
