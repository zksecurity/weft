import Glean
import Gallery

/-!
# One thing to pass around: the MPC, as a price list

An MPC is described by **what it charges**.  Features it does not offer are
absent, which is the same as infinitely expensive.  Everything else is
derived from that one value:

* `Has f M`   — `M` offers `f` (found by instance search on the literal list);
* `M.cost f`  — the price, `none` when absent;  `Has f M → M.cost f ≠ none`;
* `Ops D M`   — the signature of `M`: requests carry the `Has` evidence;
* `Circ' D M` — circuits that may only use what `M` offers.

A circuit states lower bounds, `{M} [Has .mult M]`, never a concrete `M`, so
adding features to the library or to an MPC never touches existing circuits.
-/
namespace Glean.FS
open Glean Glean.Gallery

/-- The features a functionality can offer.  Library-owned; extended by
adding constructors (the compiler then points at the two total functions
below that need a case). -/
inductive Feature where
  | lin | mult | reveal | rand | randNZ | mulTriple | cmp | inv
  deriving DecidableEq, Repr

/-- The operations of one feature (the signatures from `Glean`). -/
def Feature.Ops (D : Domain) : Feature → Sig
  | .lin => Lin D | .mult => Mult D | .reveal => Reveal D | .rand => Rand D | .randNZ => RandNZ D
  | .mulTriple => MulTriple D | .cmp => Cmp D | .inv => Inv D

/-- An MPC: the features it offers, each with its price (round latency and
communication).  Semantics is *not* here: an MPC only prices. -/
structure MPC where
  prices : List (Feature × Price)

/-- The derived cost function: `⊤` = not offered. -/
def MPC.cost (M : MPC) (f : Feature) : WithTop Price :=
  match M.prices.find? (·.1 = f) with
  | some e => (e.2 : WithTop Price)
  | none => ⊤

/-- `M` offers `f`.  Instances walk the literal price list. -/
class Has (f : Feature) (M : MPC) : Prop where
  mem : ∃ n, (f, n) ∈ M.prices

instance {f n ps} : Has f ⟨(f, n) :: ps⟩ := ⟨n, List.mem_cons_self⟩
instance {f p ps} [h : Has f ⟨ps⟩] : Has f ⟨p :: ps⟩ :=
  ⟨h.mem.choose, List.mem_cons_of_mem p h.mem.choose_spec⟩

/-- Offered means finitely priced. -/
theorem Has.finite (f : Feature) (M : MPC) [h : Has f M] : M.cost f ≠ ⊤ := by
  obtain ⟨n, hn⟩ := h.mem
  have : (M.prices.find? (·.1 = f)).isSome := by
    rw [List.find?_isSome]
    exact ⟨(f, n), hn, by simp⟩
  unfold MPC.cost
  rcases hf : M.prices.find? (·.1 = f) with _ | e
  · simp [hf] at this
  · rw [hf]; exact WithTop.coe_ne_top

/-- The signature of `M`: a request names an offered feature and one of its operations. -/
def Ops (D : Domain) (M : MPC) : Sig :=
  fun α => Σ f : { f : Feature // Has f M }, f.1.Ops D α

/-- Circuits that may use only what `M` offers. -/
abbrev Circ' (D : Domain) (M : MPC) (α : Type) := Circ (Ops D M) α

/-- Invoke an operation of feature `f`.  Does not elaborate unless `M` offers `f`. -/
def op {D : Domain} {M : MPC} (f : Feature) [Has f M] {α : Type} (o : f.Ops D α) : Circ' D M α :=
  Circ.call ⟨⟨f, inferInstance⟩, o⟩ .pure

section Ops
variable {D : Domain} {M : MPC}
def add   [Has .lin M]   (a b : D.S) : Circ' D M D.S := op .lin (Lin.add a b)
def const [Has .lin M]   (x : D.F)   : Circ' D M D.S := op .lin (Lin.const x)
def mul   [Has .mult M]  (a b : D.S) : Circ' D M D.S := op .mult (Mult.mult a b)
def reveal [Has .reveal M] (a : D.S)   : Circ' D M D.F := op .reveal (Reveal.reveal a)
def inv   [Has .inv M]   (a : D.S)   : Circ' D M D.S := op .inv (Gallery.Inv.inv a)
end Ops

/-- Subtyping: whatever `M` offers, `M'` offers too. -/
def MPC.le (M M' : MPC) : Prop := ∀ f, Has f M → Has f M'

/-- A circuit over `M` is a circuit over any `M' ≥ M`. -/
def widen {D : Domain} {M M' : MPC} (h : M.le M') {α : Type} : Circ' D M α → Circ' D M' α :=
  Circ.handle fun ⟨⟨f, hf⟩, o⟩ => Circ.call ⟨⟨f, h f hf⟩, o⟩ .pure

/-- The communication cost model of `M` is derived, not chosen: it prices
requests by feature and adds. -/
def MPC.commModel (M : MPC) {D : Domain} : CostModel (Ops D M) (WithTop ℕ) :=
  ⟨fun ⟨⟨f, _⟩, _⟩ => (M.cost f).map Price.comm⟩

/-- The latency of a feature on `M` (unsupported features never occur in a
well-typed circuit, so `⊤` maps to 0). -/
def MPC.latencyOf (M : MPC) (f : Feature) : Nat := (M.cost f).elim 0 Price.delay

/-- Every well-typed circuit has finite cost on its MPC: each request carries
`Has`, hence a finite price, and a sum in `WithTop ℕ` is `⊤` only if a term is. -/
theorem cost_finite {D : Domain} {M : MPC} {L α : Type} (Mo : Model (Ops D M) L Id)
    (c : Circ' D M α) : cost Mo M.commModel c ≠ ⊤ := by
  induction c with
  | pure a => exact WithTop.zero_ne_top
  | call o k ih =>
    obtain ⟨⟨f, hf⟩, o⟩ := o
    show M.commModel.op ⟨⟨f, hf⟩, o⟩ + cost Mo M.commModel (k _) ≠ ⊤
    refine WithTop.add_ne_top.2 ⟨?_, ih _⟩
    have := Has.finite f M
    rcases h : M.cost f with _ | p
    · exact absurd h this
    · simp [MPC.commModel, h]

/-- The ideal model is per feature, once, and assembled for any `M`.  An MPC
only prices; it never redefines semantics.  (The semantics, in `PMF`.) -/
noncomputable def Feature.ideal (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Zero F] [Nontrivial F] [DecidableEq F] [Fintype F] : (f : Feature) → Model (f.Ops (.ideal F)) F PMF
  | .lin => (Lin.ideal F).lift PMF | .mult => (Mult.ideal F).lift PMF
  | .reveal => (Reveal.ideal F).lift PMF | .rand => Rand.ideal F | .randNZ => RandNZ.ideal F
  | .mulTriple => MulTriple.ideal F | .cmp => (Cmp.ideal F).lift PMF
  | .inv => (⟨fun o => match o with | .inv x => pure x, fun _ _ => []⟩ : Model _ F Id).lift PMF

noncomputable def MPC.ideal (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Zero F] [Nontrivial F] [DecidableEq F] [Fintype F] (M : MPC) : Model (Ops (.ideal F) M) F PMF where
  program  := fun ⟨⟨f, _⟩, o⟩ => (Feature.ideal F f).program o
  leak := fun ⟨⟨f, _⟩, o⟩ x => (Feature.ideal F f).leak o x

/-- The evaluation model (coins fixed), for costs by `rfl`. -/
def Feature.eval (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Inhabited F] : (f : Feature) → Model (f.Ops (.ideal F)) F Id
  | .lin => Lin.ideal F | .mult => Mult.ideal F | .reveal => Reveal.ideal F | .rand => Rand.eval F
  | .randNZ => ⟨fun o => match o with | .randNZ => pure default, fun _ _ => []⟩
  | .mulTriple => MulTriple.eval F | .cmp => Cmp.ideal F
  | .inv => ⟨fun o => match o with | .inv x => pure x, fun _ _ => []⟩

def MPC.eval (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Inhabited F] (M : MPC) : Model (Ops (.ideal F) M) F Id where
  program  := fun ⟨⟨f, _⟩, o⟩ => (Feature.eval F f).program o
  leak := fun ⟨⟨f, _⟩, o⟩ x => (Feature.eval F f).leak o x

/-! ## Using it -/

/-- The circuit's type states what it needs, as lower bounds on `M`. -/
def mulAdd {D : Domain} {M : MPC} [Has .lin M] [Has .mult M] (a b c : D.S) : Circ' D M D.S := do
  let p ← mul a b
  add p c

def invAdd {D : Domain} {M : MPC} [Has .lin M] [Has .inv M] (a b : D.S) : Circ' D M D.S := do
  let x ← inv a
  add x b

/-- Two MPCs.  Only the price list differs; semantics and features are shared. -/
abbrev honestMajority : MPC :=
  ⟨[(.lin, ⟨0, 0⟩), (.mult, ⟨1, 2⟩), (.reveal, ⟨1, 1⟩), (.rand, ⟨0, 0⟩), (.randNZ, ⟨0, 0⟩), (.cmp, ⟨3, 10⟩)]⟩
abbrev withInversion  : MPC :=
  ⟨[(.lin, ⟨0, 0⟩), (.mult, ⟨1, 2⟩), (.reveal, ⟨1, 1⟩), (.rand, ⟨0, 0⟩), (.randNZ, ⟨0, 0⟩), (.cmp, ⟨3, 10⟩),
    (.inv, ⟨1, 3⟩)]⟩

-- `mulAdd` runs on both; `invAdd` only where inversion is offered.
example {D : Domain} (a b c : D.S) : Circ' D honestMajority D.S := mulAdd a b c
example {D : Domain} (a b c : D.S) : Circ' D withInversion D.S := mulAdd a b c
example {D : Domain} (a b : D.S)   : Circ' D withInversion D.S := invAdd a b
-- example {D : Domain} (a b : D.S) : Circ' D honestMajority D.S := invAdd a b
--   -- error: failed to synthesize Has Feature.inv honestMajority

-- The price of a feature is data; absence is `none`.
example : honestMajority.cost .mult = (⟨1, 2⟩ : Price) := rfl
example : honestMajority.cost .inv = ⊤ := rfl
example : withInversion.cost .inv = (⟨1, 3⟩ : Price) := rfl

/-- The timed model of `M`: each feature's timed semantics at the latency `M` charges for it. -/
def Feature.timed (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Inhabited F] : (f : Feature) → Nat → Model (f.Ops (Domain.timed F)) F Sched
  | .lin, _ => Lin.timed F | .mult, ℓ => Mult.timed F ℓ | .reveal, ℓ => Reveal.timed F ℓ
  | .rand, _ => Rand.timed F | .mulTriple, ℓ => MulTriple.timed F ℓ
  | .randNZ, _ => ⟨fun o => match o with | .randNZ => fun s => (⟨default, s.clock⟩, s), fun _ _ => []⟩
  | .cmp, ℓ => Gallery.Cmp.timed F ℓ | .inv, ℓ => Gallery.Inv.timed F ℓ

def MPC.timed (F : Type) [Add F] [Mul F] [Sub F] [LT F] [DecidableLT F] [OfNat F 0] [OfNat F 1]
    [Inhabited F] (M : MPC) : Model (Ops (Domain.timed F) M) F Sched where
  program := fun ⟨⟨f, _⟩, o⟩ => (Feature.timed F f (M.latencyOf f)).program o
  leak := fun ⟨⟨f, _⟩, o⟩ x => (Feature.timed F f (M.latencyOf f)).leak o x

-- Communication is evaluated against the MPC's derived cost model; delay against its timed model.
example (a b c : Int) :
    cost (honestMajority.eval Int) honestMajority.commModel (mulAdd (D := .ideal Int) a b c) = 2 := rfl
example (a b c : Int) :
    delayOn (honestMajority.timed Int) (mulAdd (D := .timed Int) ⟨a, 0⟩ ⟨b, 0⟩ ⟨c, 0⟩) = 1 := rfl
example (a b : Int) :
    cost (withInversion.eval Int) withInversion.commModel (invAdd (D := .ideal Int) a b) = 3 := rfl

/-- Delay does not stack when work is independent: four multiplications
written one after another take 1 round and 4× the communication; four
dependent ones take 4 rounds and the same communication. -/
def fourPar {D : Domain} {M : MPC} [Has .mult M] (a b : D.S) : Circ' D M (List D.S) :=
  [mul a b, mul a b, mul a b, mul a b].mapM id
def fourSeq {D : Domain} {M : MPC} [Has .mult M] (a b : D.S) : Circ' D M D.S := do
  let x ← mul a b; let y ← mul x b; let z ← mul y b; mul z b
example (a b : Int) :
    cost (honestMajority.eval Int) honestMajority.commModel (fourPar (D := .ideal Int) a b) = 8 := rfl
example (a b : Int) :
    (Sched.output (honestMajority.timed Int) (fourPar (D := .timed Int) ⟨a, 0⟩ ⟨b, 0⟩)).map Timed.time
      = [1, 1, 1, 1] := rfl
example (a b : Int) :
    cost (honestMajority.eval Int) honestMajority.commModel (fourSeq (D := .ideal Int) a b) = 8 := rfl
example (a b : Int) :
    delayOn (honestMajority.timed Int) (fourSeq (D := .timed Int) ⟨a, 0⟩ ⟨b, 0⟩) = 4 := rfl

-- Subtyping, checked by `decide`-free reasoning: every feature of the smaller
-- MPC is in the larger list (here the larger list literally extends it).
theorem hm_le_wi : honestMajority.le withInversion := by
  intro f h
  obtain ⟨n, hn⟩ := h.mem
  have e : withInversion.prices = honestMajority.prices ++ [(.inv, ⟨1, 3⟩)] := rfl
  exact ⟨n, e ▸ List.mem_append_left _ hn⟩

example {D : Domain} (a b c : D.S) : Circ' D withInversion D.S :=
  widen hm_le_wi (mulAdd (M := honestMajority) a b c)

/-! ## Adding a feature later

Adding `shuffle` means: one constructor in `Feature`, one case in each of
`Feature.Ops` and `Feature.ideal`, and one price in the MPCs that offer it.
Nothing above this comment changes: circuits state lower bounds, MPCs are
lists, and `MPC.cost` returns `none` for anything not listed.  The three
checks below are the invariant, with `withInversion` standing in for "an
MPC that gained a feature". -/

abbrev grown : MPC := ⟨(.mulTriple, ⟨0, 0⟩) :: withInversion.prices⟩
example {D : Domain} (a b c : D.S) : Circ' D grown D.S := mulAdd a b c        -- old circuit, new MPC
example (a b c : Int) :
    cost (grown.eval Int) grown.commModel (mulAdd (D := .ideal Int) a b c) = 2 := rfl   -- old price
example {D : Domain} (a b c : D.S) : Circ' D grown D.S :=
  widen (fun _ h => ⟨h.mem.choose, List.mem_cons_of_mem _ h.mem.choose_spec⟩)
    (mulAdd (M := withInversion) a b c)                                        -- old coercion

end Glean.FS
