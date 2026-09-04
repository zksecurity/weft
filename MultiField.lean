import Features
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Generic over the field: shares as a type constructor

Shares are a type constructor: `D.S F` is "a share of an `F`".  Every
operation is generic over `F`, the field's algebra is a Mathlib typeclass
on `F`, and switching is a capability over two field types.  The MPC's
price list pairs a feature with the field it is offered on, and the entry
carries the field's instances, so the ideal model can be assembled for any
MPC.

What the ideal model needs of a field, all from Mathlib: `CommRing F` for
the arithmetic (`Field` where inversion is used), an order `LT F` for
`cmp` (on `ZMod n`, the order of canonical representatives), and
`Encodable F` to put coins and leaked values of every field on one `ℕ`
alphabet (`ZMod.val` and `Nat.cast` on `ZMod n`).
-/
namespace Glean.MF
open Glean Glean.FS

/-- The circuit's view of shares: an opaque type constructor. -/
structure Domain where
  S : Type → Type

/-- The single-field domain of `Glean` at a particular field. -/
abbrev Domain.at (D : Domain) (F : Type) : Glean.Domain := ⟨F, D.S F⟩

/-- Ideal domain: a share of an `F` is an `F`. -/
abbrev Domain.ideal : Domain := ⟨fun F => F⟩

/-- Share conversion between two fields. -/
inductive Switch (D : Domain) (F G : Type) : Sig where
  | switch : D.S F → Switch D F G (D.S G)

/-! ### `ZMod n` as a concrete field: order and encoding by canonical representative -/

instance {n : ℕ} [NeZero n] : LT (ZMod n) := ⟨fun a b => a.val < b.val⟩
instance {n : ℕ} [NeZero n] : DecidableRel (α := ZMod n) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))
instance {n : ℕ} [NeZero n] : Encodable (ZMod n) where
  encode := ZMod.val
  decode k := some (k : ZMod n)
  encodek a := by simp [ZMod.natCast_zmod_val]

/-- `𝔽₂` is `ZMod 2`: `+` is xor, `*` is and, literals `0` and `1`. -/
abbrev GF2 := ZMod 2

/-- An edaBit: a random `r < 2^m` shared over `F`, together with its `m` bits
shared over `𝔽₂` (least significant first).  A correlation across two fields. -/
inductive EdaBit (D : Domain) (F : Type) (m : Nat) : Sig where
  | get : EdaBit D F m (D.S F × (Fin m → D.S GF2))

/-- A daBit (Rotaru–Wood, ePrint 2019/207): one uniformly random bit `b`,
shared over `F` *and* over `𝔽₂`.  The simplest correlation across two
fields, and the one behind Boolean ↔ arithmetic conversion. -/
inductive DaBit (D : Domain) (F : Type) : Sig where
  | get : DaBit D F (D.S F × D.S GF2)

/-- A capability: a feature on a field, switching between two, or a
cross-field correlation.  The field's instances travel with the entry. -/
inductive Cap where
  | on (f : Feature) (F : Type) [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F]
       [Fintype F] [DecidableEq F] [Nontrivial F]
  | switch (F G : Type) [CommRing F] [Encodable F] [CommRing G]
  | edabit (F : Type) [CommRing F] (m : Nat)
  | dabit (F : Type) [CommRing F]

def Cap.Ops (D : Domain) : Cap → Sig
  | @Cap.on f F _ _ _ _ _ _ _ => f.Ops (D.at F)
  | @Cap.switch F G _ _ _ => Switch D F G
  | @Cap.edabit F _ m => EdaBit D F m
  | @Cap.dabit F _ => DaBit D F

structure MPC where
  prices : List (Cap × Price)

/-- `M` offers `c`, at a price.  The price is *data* carried by the evidence. -/
class Has (c : Cap) (M : MPC) where
  price : Price
  mem   : (c, price) ∈ M.prices
instance {c p ps} : Has c ⟨(c, p) :: ps⟩ := ⟨p, List.mem_cons_self⟩
instance {c q ps} [h : Has c ⟨ps⟩] : Has c ⟨q :: ps⟩ := ⟨h.price, List.mem_cons_of_mem q h.mem⟩

/-- The signature of `M`: a request names a capability, carries the evidence
(with its price) that `M` offers it, and one of its operations. -/
def Ops (D : Domain) (M : MPC) : Sig.{1} :=
  fun α => Σ c : Cap, Has c M × c.Ops D α
abbrev Circ' (D : Domain) (M : MPC) (α : Type) := Circ (Ops D M) α

def op {D : Domain} {M : MPC} (c : Cap) [h : Has c M] {α : Type} (o : c.Ops D α) : Circ' D M α :=
  Circ.call ⟨c, h, o⟩ .pure

-- Operations: generic over the field, which is inferred from the share's type.
section Ops
variable {D : Domain} {M : MPC} {F G : Type}
  [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F] [Fintype F] [DecidableEq F] [Nontrivial F]
  [CommRing G] [LT G] [DecidableRel (α := G) (· < ·)] [Encodable G] [Fintype G] [DecidableEq G] [Nontrivial G]
def add   [Has (.on .lin F) M]  (a b : D.S F) : Circ' D M (D.S F) := op (.on .lin F) (Lin.add a b)
def sub   [Has (.on .lin F) M]  (a b : D.S F) : Circ' D M (D.S F) := op (.on .lin F) (Lin.sub a b)
def const [Has (.on .lin F) M]  (x : F)       : Circ' D M (D.S F) := op (.on .lin F) (Lin.const x)
def smul  [Has (.on .lin F) M]  (x : F) (a : D.S F) : Circ' D M (D.S F) := op (.on .lin F) (Lin.smul x a)
def mul   [Has (.on .mult F) M] (a b : D.S F) : Circ' D M (D.S F) := op (.on .mult F) (Mult.mult a b)
def lt    [Has (.on .cmp F) M]  (a b : D.S F) : Circ' D M (D.S F) := op (.on .cmp F) (Cmp.lt a b)
def reveal [Has (.on .reveal F) M] (a : D.S F) : Circ' D M F := op (.on .reveal F) (Reveal.reveal a)
/-- A random share *of `F`*: nothing determines the field, so it is passed. -/
def rand  (F : Type) [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F]
    [Fintype F] [DecidableEq F] [Nontrivial F]
    [Has (.on .rand F) M] : Circ' D M (D.S F) := op (.on .rand F) Rand.rand
def randNZ (F : Type) [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F]
    [Fintype F] [DecidableEq F] [Nontrivial F]
    [Has (.on .randNZ F) M] : Circ' D M (D.S F) := op (.on .randNZ F) RandNZ.randNZ
def switch (G : Type) [CommRing G] [Has (.switch F G) M] (a : D.S F) : Circ' D M (D.S G) :=
  op (.switch F G) (Switch.switch a)
def edabit (F : Type) [CommRing F] (m : Nat) [Has (.edabit F m) M] : Circ' D M (D.S F × (Fin m → D.S GF2)) :=
  op (.edabit F m) EdaBit.get
def dabit (F : Type) [CommRing F] [Has (.dabit F) M] : Circ' D M (D.S F × D.S GF2) :=
  op (.dabit F) DaBit.get
end Ops

/-! ## Semantics, once, for every MPC -/

/-- The `m` low bits of `n` as elements of `𝔽₂`, least significant first. -/
def bitsOf (m : Nat) (n : Nat) : Fin m → GF2 := fun i => if n.testBit i then 1 else 0

/-- Ideal model of a capability (the semantics, in `PMF`), with `ℕ` leakage:
leaked values leave their field by `encode`.  An edaBit is a uniform
`r < 2^m` together with its bits. -/
noncomputable def Cap.ideal : (c : Cap) → Model (c.Ops .ideal) Nat PMF
  | @Cap.on f F _ _ _ _ _ _ _ => (Feature.ideal F f).mapLeak Encodable.encode
  | @Cap.switch F G _ _ _ => ⟨fun o => match o with
      | .switch x => pure ((Encodable.encode x : ℕ) : G),   -- the canonical representative, if in range
      fun _ _ => []⟩
  | @Cap.edabit F _ m => ⟨fun o => match o with
      | .get => (uniform (Fin (2 ^ m))).map fun r => ((r.val : F), bitsOf m r.val),
      fun _ _ => []⟩
  | @Cap.dabit F _ => ⟨fun o => match o with
      | .get => (uniform GF2).map fun (b : ZMod 2) => ((b.val : F), (b : GF2)),   -- one bit, seen in both fields
      fun _ _ => []⟩

noncomputable def MPC.ideal (M : MPC) : Model (Ops .ideal M) Nat PMF where
  program := fun ⟨c, _, o⟩ => (Cap.ideal c).program o
  leak := fun ⟨c, _, o⟩ x => (Cap.ideal c).leak o x

/-- Evaluation model: coins fixed (`coin` is the edaBit's value, for
examples that want to see a particular mask). -/
def Cap.eval (coin : Nat) : (c : Cap) → Model (c.Ops .ideal) Nat Id
  | @Cap.on f F _ _ _ _ _ _ _ =>
    haveI : Inhabited F := ⟨0⟩
    (Feature.eval F f).mapLeak Encodable.encode
  | @Cap.switch F G _ _ _ => ⟨fun o => match o with
      | .switch x => pure ((Encodable.encode x : ℕ) : G),
      fun _ _ => []⟩
  | @Cap.edabit F _ m => ⟨fun o => match o with
      | .get => let r := coin % 2 ^ m; pure ((r : F), bitsOf m r),
      fun _ _ => []⟩
  | @Cap.dabit F _ => ⟨fun o => match o with
      | .get => let b := coin % 2; pure ((b : F), (b : GF2)),
      fun _ _ => []⟩

def MPC.eval (M : MPC) (coin : Nat := 0) : Model (Ops .ideal M) Nat Id where
  program := fun ⟨c, _, o⟩ => (Cap.eval coin c).program o
  leak := fun ⟨c, _, o⟩ x => (Cap.eval coin c).leak o x

/-- The communication cost model reads the price off the evidence in each
request: total and finite for every well-typed circuit. -/
def MPC.commModel (M : MPC) {D : Domain} : CostModel (Ops D M) Nat :=
  ⟨fun ⟨_, h, _⟩ => h.price.comm⟩

/-! ### The timed domain, per capability -/

/-- The multi-field timed domain: a share of an `F` carries its ready time. -/
abbrev Domain.timed : Domain := ⟨fun F => Timed F⟩

/-- Timed semantics of a capability at latency `ℓ`. -/
def Cap.timed : (c : Cap) → Nat → Model (c.Ops Domain.timed) Nat Sched
  | @Cap.on f F _ _ _ _ _ _ _, ℓ =>
    haveI : Inhabited F := ⟨0⟩
    (FS.Feature.timed F f ℓ).mapLeak Encodable.encode
  | @Cap.switch F G _ _ _, ℓ => ⟨fun o => match o with
      | .switch x => Timed.after [x.time] ℓ ((Encodable.encode x.val : ℕ) : G),
      fun _ _ => []⟩
  | @Cap.edabit F _ m, ℓ => ⟨fun o => match o with
      | .get => fun s => ((⟨(0 : F), s.clock + ℓ⟩, fun i => ⟨bitsOf m 0 i, s.clock + ℓ⟩), s),
      fun _ _ => []⟩
  | @Cap.dabit F _, ℓ => ⟨fun o => match o with
      | .get => fun s => ((⟨(0 : F), s.clock + ℓ⟩, ⟨0, s.clock + ℓ⟩), s),
      fun _ _ => []⟩

/-- The timed model of `M`: each capability at the latency `M` charges for it. -/
def MPC.timed (M : MPC) : Model (Ops Domain.timed M) Nat Sched where
  program := fun ⟨c, h, o⟩ => (Cap.timed c h.price.delay).program o
  leak := fun ⟨c, h, o⟩ x => (Cap.timed c h.price.delay).leak o x

/-! ## A field circuit, generic over the field -/

/-- Inversion by masking, over any field `F` the MPC offers these features on.
`Inv F` is what the clear-side computation needs (Mathlib's; on `ZMod p` it
is the field inverse). -/
def invert {D : Domain} {M : MPC} {F : Type}
    [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F] [Fintype F] [DecidableEq F] [Nontrivial F]
    [Inv F]
    [Has (.on .lin F) M] [Has (.on .mult F) M] [Has (.on .randNZ F) M] [Has (.on .reveal F) M]
    (x : D.S F) : Circ' D M (D.S F) := do
  let s ← randNZ F
  let v ← mul x s
  let m ← reveal v
  smul m⁻¹ s

/-! ## Example: generic over two fields, comparison offered on the second -/

/-- Multiply in `F`, switch to `G` where comparison is offered, compare, switch back. -/
def mulThenCompare {D : Domain} {M : MPC} {F G : Type}
    [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F] [Fintype F] [DecidableEq F] [Nontrivial F]
    [CommRing G] [LT G] [DecidableRel (α := G) (· < ·)] [Encodable G] [Fintype G] [DecidableEq G] [Nontrivial G]
    [Has (.on .mult F) M] [Has (.switch F G) M] [Has (.on .cmp G) M] [Has (.switch G F) M]
    (a b c : D.S F) : Circ' D M (D.S F) := do
  let ab ← mul a b                              -- in F
  let ab' ← switch G ab                         -- conversions: independent, so one round
  let c' ← switch G c
  let bit ← lt ab' c'                           -- comparison is offered on G
  switch F bit                                  -- back in F

instance : Fact (1 < 2) := ⟨by decide⟩
instance : Fact (1 < 7) := ⟨by decide⟩
instance : Fact (1 < 16) := ⟨by decide⟩
instance : Fact (1 < 17) := ⟨by decide⟩

/-- An MPC over `𝔽₇` and `ℤ/16`. -/
abbrev twoField : MPC := ⟨[
  (.on .lin (ZMod 7), ⟨0, 0⟩), (.on .mult (ZMod 7), ⟨1, 2⟩), (.on .reveal (ZMod 7), ⟨1, 1⟩),
  (.on .lin (ZMod 16), ⟨0, 0⟩), (.on .mult (ZMod 16), ⟨1, 2⟩), (.on .cmp (ZMod 16), ⟨2, 6⟩),
  (.switch (ZMod 7) (ZMod 16), ⟨3, 8⟩), (.switch (ZMod 16) (ZMod 7), ⟨2, 4⟩)]⟩

-- Nothing is revealed; communication adds; delay is the critical path: the switch
-- of `c` overlaps the multiplication and the switch of `ab` (1 + 3 + 2 + 2 = 8).
example (a b c : ZMod 7) :
    leak twoField.eval (mulThenCompare (D := .ideal) (M := twoField) (F := ZMod 7) (G := ZMod 16) a b c) = [] := rfl
example (a b c : ZMod 7) :
    cost twoField.eval twoField.commModel (mulThenCompare (D := .ideal) (M := twoField) (F := ZMod 7) (G := ZMod 16) a b c)
      = 28 := rfl
example (a b c : ZMod 7) :
    (Sched.output twoField.timed (mulThenCompare (D := .timed) (M := twoField) (F := ZMod 7) (G := ZMod 16) ⟨a, 0⟩ ⟨b, 0⟩ ⟨c, 0⟩)).time
      = 8 := rfl
-- 2·3 = 6 in 𝔽₇, compared with 5 in ℤ/16: not less, so 0.
example : (output twoField.eval (mulThenCompare (D := .ideal) (M := twoField) (F := ZMod 7) (G := ZMod 16) 2 3 5) : ZMod 7) = 0 := by
  decide

-- `invert` on the `𝔽₇` field: two rounds, one revealed value `x · s`.
abbrev withRand : MPC := ⟨(.on .randNZ (ZMod 7), ⟨0, 0⟩) :: twoField.prices⟩
example (x : ZMod 7) :
    cost withRand.eval withRand.commModel (invert (D := .ideal) (M := withRand) (F := ZMod 7) x) = 3 := rfl
example (x : ZMod 7) :
    (Sched.output withRand.timed (invert (D := .timed) (M := withRand) (F := ZMod 7) ⟨x, 0⟩)).time = 2 := rfl
-- The semantics: a uniform nonzero mask `s`; what is revealed is `x · s` (as its
-- representative); the output is `s / (x · s)`.
example (x : ZMod 7) :
    dist withRand.ideal (invert (D := .ideal) (M := withRand) (F := ZMod 7) x)
      = (uniform {s : ZMod 7 // s ≠ 0}).bind fun s => pure ((x * s.1)⁻¹ * s.1, [(x * s.1).val]) := by
  simp [dist, invert, MPC.ideal, Cap.ideal, Feature.ideal, Model.mapLeak, Lin.ideal, Mult.ideal, Reveal.ideal,
    RandNZ.ideal, randNZ, mul, reveal, smul, MF.op, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, Encodable.encode]

/-! ## Example: arithmetic → binary conversion with an edaBit -/

/-- Ripple-carry addition of a *public* `c` (as bits) to shared bits, over
`𝔽₂` shares: xor is free (`lin`), and is a round (`mult`).  `m` rounds. -/
def addPublic {D : Domain} {M : MPC} [Has (.on .lin GF2) M] [Has (.on .mult GF2) M] :
    (m : Nat) → (Fin m → GF2) → (Fin m → D.S GF2) → D.S GF2 → Circ' D M (Fin m → D.S GF2)
  | 0, _, _, _ => pure fun i => i.elim0
  | m + 1, c, r, carry => do
    let t ← add (r 0) carry                   -- r₀ ⊕ carry
    let cb ← const (c 0)
    let s ← add t cb                          -- s₀ = c₀ ⊕ r₀ ⊕ carry
    let rc ← mul (r 0) carry                  -- r₀ ∧ carry          (the one round)
    let ct ← smul (c 0) t                     -- c₀ ∧ (r₀ ⊕ carry)   (public bit: free)
    let carry' ← add rc ct                    -- maj(c₀, r₀, carry), branch-free
    let rest ← addPublic m (Fin.tail c) (Fin.tail r) carry'
    pure (Fin.cons s rest)

/-- A2B: reveal `x - r`, then `x = (x - r) + r` bit by bit, with `r`'s bits
already shared over `𝔽₂`.  One reveal round, then `m` rounds of the adder. -/
def a2b {D : Domain} {M : MPC} {F : Type}
    [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F] [Fintype F] [DecidableEq F] [Nontrivial F]
    (m : Nat)
    [Has (.edabit F m) M] [Has (.on .lin F) M] [Has (.on .reveal F) M]
    [Has (.on .lin GF2) M] [Has (.on .mult GF2) M]
    (x : D.S F) : Circ' D M (Fin m → D.S GF2) := do
  let (r, rbits) ← edabit F m
  let d ← sub x r
  let c ← reveal d                             -- the only revealed value: x - r
  let zero ← const (0 : GF2)
  addPublic m (bitsOf m (Encodable.encode c)) rbits zero

/-- A mixed `𝔽₁₇` / `𝔽₂` MPC with 4-bit edaBits from preprocessing. -/
abbrev mixed : MPC := ⟨[
  (.on .lin (ZMod 17), ⟨0, 0⟩), (.on .mult (ZMod 17), ⟨1, 2⟩), (.on .reveal (ZMod 17), ⟨1, 1⟩),
  (.on .lin GF2, ⟨0, 0⟩), (.on .mult GF2, ⟨1, 1⟩),
  (.edabit (ZMod 17) 4, ⟨0, 0⟩)]⟩

-- What is revealed: `x - r`, as its representative (evaluation with the mask `r = 3`).
example (x : ZMod 17) :
    leak (mixed.eval 3) (a2b (D := .ideal) (M := mixed) (F := ZMod 17) 4 x) = [(x - 3).val] := rfl
-- Communication: one reveal and four ANDs.  Delay of the last bit: the reveal,
-- then three carries (the fourth AND only feeds the unused carry-out).
example : cost (mixed.eval 3) mixed.commModel (a2b (D := .ideal) (M := mixed) (F := ZMod 17) 4 5) = 5 := by
  decide
example : ((Sched.output mixed.timed (a2b (D := .timed) (M := mixed) (F := ZMod 17) 4 ⟨5, 0⟩)) 3).time = 4 := by
  decide
-- Correctness on instances: the bits of 5 = 0b0101, under two different masks.
-- This simplified A2B omits the modular correction of the real edaBit protocol
-- (a binary compare-and-subtract of `p` when `x - r` wraps), so it is correct
-- under the assumption `r ≤ x`; `decide` refutes the mask 14 case, as it should.
example : (output (mixed.eval 3) (a2b (D := .ideal) (M := mixed) (F := ZMod 17) 4 5) : Fin 4 → ZMod 2) = ![1, 0, 1, 0] := by
  decide
example : (output (mixed.eval 1) (a2b (D := .ideal) (M := mixed) (F := ZMod 17) 4 5) : Fin 4 → ZMod 2) = ![1, 0, 1, 0] := by
  decide

/-! ## Example: daBits, and a circuit that spans two fields

A daBit is a bit `b` shared in both worlds.  With one daBit, a Boolean
share `⟦x⟧₂` becomes an arithmetic share `⟦x⟧_F` at the cost of one
reveal: open `c = x ⊕ b` in `𝔽₂` (a uniform bit, so it says nothing about
`x`), then `x = c + b − 2·c·b` in `F`, which is linear in `⟦b⟧_F` once `c`
is public.  Chained through a list, the conversions are independent
(one reveal round in total), and the sum in `F` is free: a Hamming
weight computed with Boolean shares in, an arithmetic share out. -/

section DaBits
variable {D : Domain} {M : MPC} {F : Type}
  [CommRing F] [LT F] [DecidableRel (α := F) (· < ·)] [Encodable F] [Fintype F] [DecidableEq F] [Nontrivial F]

/-- Boolean → arithmetic with one daBit. -/
def b2a [Has (.dabit F) M] [Has (.on .lin GF2) M] [Has (.on .reveal GF2) M] [Has (.on .lin F) M]
    (x : D.S GF2) : Circ' D M (D.S F) := do
  let (bF, b₂) ← dabit F
  let m ← add x b₂                    -- x ⊕ b, over 𝔽₂
  let c ← reveal m                    -- the one revealed value: a uniform bit
  let cF ← const (c.val : F)          -- c, as an element of F
  let s ← add cF bF                   -- c + b
  let t ← smul (2 * (c.val : F)) bF   -- 2·c·b, linear: c is public
  sub s t                             -- x = c + b − 2cb

/-- Free sum over `F`. -/
def sumF [Has (.on .lin F) M] : List (D.S F) → Circ' D M (D.S F)
  | [] => const (0 : F)
  | [y] => pure y
  | y :: ys => do let s ← sumF ys; add y s

/-- Hamming weight: bits in, arithmetic share out.  All conversions in one
round, then a free sum. -/
def hammingWeight [Has (.dabit F) M] [Has (.on .lin GF2) M] [Has (.on .reveal GF2) M] [Has (.on .lin F) M]
    (xs : List (D.S GF2)) : Circ' D M (D.S F) := do
  let ys ← xs.mapM b2a
  sumF ys
end DaBits

/-- An MPC over `𝔽₁₇` and `𝔽₂` with daBits from preprocessing. -/
abbrev withDaBits : MPC := ⟨[
  (.on .lin (ZMod 17), ⟨0, 0⟩), (.on .mult (ZMod 17), ⟨1, 2⟩), (.on .reveal (ZMod 17), ⟨1, 1⟩),
  (.on .lin GF2, ⟨0, 0⟩), (.on .reveal GF2, ⟨1, 1⟩),
  (.dabit (ZMod 17), ⟨0, 0⟩)]⟩

-- What is revealed: `x ⊕ b` (evaluation with the daBit fixed to `b = 1`); nothing else.
example (x : GF2) : leak (withDaBits.eval 1) (b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) x) = [(x + 1).val] := rfl
-- Correctness on instances, for both values of the daBit.
example : (output (withDaBits.eval 0) (b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) 1) : ZMod 17) = 1 := by decide
example : (output (withDaBits.eval 1) (b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) 1) : ZMod 17) = 1 := by decide
example : (output (withDaBits.eval 1) (b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) 0) : ZMod 17) = 0 := by decide
-- The Hamming weight of `1, 0, 1, 1` is 3, in 𝔽₁₇; three reveals; one round, not four.
example : (output (withDaBits.eval 1) (hammingWeight (D := .ideal) (M := withDaBits) (F := ZMod 17) [1, 0, 1, 1]) : ZMod 17) = 3 := by
  decide
example : cost (withDaBits.eval 1) withDaBits.commModel
    (hammingWeight (D := .ideal) (M := withDaBits) (F := ZMod 17) [1, 0, 1, 1]) = 4 := by decide
example : (Sched.output withDaBits.timed
    (hammingWeight (D := .timed) (M := withDaBits) (F := ZMod 17) [⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩])).time = 1 := by
  decide

/-- The semantics of `b2a`: draw a uniform bit `b`, reveal `x + b`, output `x` in `F`. -/
theorem b2a_dist (x : GF2) :
    dist withDaBits.ideal (b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) x)
      = (uniform GF2).bind fun b => pure ((x.val : ZMod 17), [(x + b).val]) := by
  -- correctness of the reconstruction, for both values of `x` and of the daBit
  have out : ∀ b : GF2, (ZMod.cast (x + b) : ZMod 17) + ZMod.cast b - 2 * ZMod.cast (x + b) * ZMod.cast b
      = ZMod.cast x := by
    intro b; fin_cases x <;> fin_cases b <;> decide
  simp [dist, b2a, MPC.ideal, Cap.ideal, Feature.ideal, Model.mapLeak, Lin.ideal, Reveal.ideal,
    dabit, add, reveal, const, smul, sub, MF.op, run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, Encodable.encode]
  congr 1
  funext b
  rw [out b]

/-- **Hiding.**  The revealed bit `x + b` is uniform for either `x`: `b ↦ x + b`
is a bijection of `𝔽₂`; the simulator flips a coin. -/
theorem b2a_hiding :
    Hiding withDaBits.ideal (fun x : GF2 => b2a (D := .ideal) (M := withDaBits) (F := ZMod 17) x) := by
  refine ⟨fun _ => (uniform GF2).map fun t => [t.val], fun x => ?_⟩
  have out : Prod.fst <$> ((uniform GF2).bind fun b => (pure ((x.val : ZMod 17), [(x + b).val]) : PMF _))
      = pure (x.val : ZMod 17) := by
    simp [PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  rw [b2a_dist, out, pure_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_map]
  conv_rhs => rw [← uniform_map_equiv (Equiv.addLeft x), PMF.bind_map]
  rfl

end Glean.MF
