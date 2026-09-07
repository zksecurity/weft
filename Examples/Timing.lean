import Weft
import Examples.Basic

/-!
# Data and control dependencies

Requests with independent operands can overlap,
even when written sequentially in `do` notation.
Reading a clear value with `Prog.look` adds a control dependency to later requests.

The composition examples compare three models of `a·b + c`:
a fixed latency, an input timing profile, and a derived implementation model.
The fixed latency waits for all operands before charging for multiplication.
The profile permits multiplication to overlap the arrival of `c`.

The derived model runs the implementation with the caller's scheduling state.
`Realizations.delayOn_timed` proves agreement with inlining;
a custom profile needs a separate correctness argument for the states in which it is used.
-/
namespace Weft.Examples.Timing
open Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- Multiply two independent pairs, then multiply their results. -/
def mul4seq [Has (Mult F) fs] (a b c d : D.share F) : Prog fs.ops D (D.share F) := do
  let ab ← mul a b
  let cd ← mul c d
  mul ab cd

/-- Three multiplications, each depending on the previous result. -/
def chain3 [Has (Mult F) fs] (a b c d : D.share F) : Prog fs.ops D (D.share F) := do
  let x ← mul a b
  let y ← mul x c
  mul y d

/-- Propagate an opening's availability time through clear arithmetic and `const`. -/
def revealThenUse [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] (a b c : D.share F) (k : D.clear F) :
    Prog fs.ops D (D.share F) := do
  let p ← mul a b
  let v ← reveal p
  let t ← const (v * k)
  mul t c

/-- Issue two openings without reading either value.
Both use the same control clock and have no data dependency on each other. -/
def revealBoth [Has (Reveal F) fs] (v₁ v₂ : D.share F) : Prog fs.ops D (D.clear F × D.clear F) := do
  let a ← reveal v₁
  let b ← reveal v₂
  pure (a, b)
/-- Read the first opening before issuing the second.
The read creates a control dependency between them. -/
def revealBothLook [Has (Reveal F) fs] (v₁ v₂ : D.share F) : Prog fs.ops D (D.clear F × D.clear F) := do
  let a ← reveal v₁
  Prog.look a fun _ => do
    let b ← reveal v₂
    pure (a, b)
/-- Use the first opening as a scalar without reading it through `look`.
The second opening remains independent. -/
def revealUseReveal [Has (Lin F) fs] [Has (Reveal F) fs] (v₁ v₂ x : D.share F) : Prog fs.ops D (D.share F × D.clear F) := do
  let a ← reveal v₁
  let b ← reveal v₂
  let y ← smul a x
  pure (y, b)
end Programs

section
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

-- The pair products overlap, giving two multiplication layers.
example (a b c d : F) : delayOn (Std.timed F) (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 2 := rfl
-- The chain has three multiplication layers.
example (a b c d : F) : delayOn (Std.timed F) (chain3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 3 := rfl
-- Reveal at 2, clear computation, `const` at 2, multiplication at 3.
example (a b c k : F) : delayOn (Std.timed F) (revealThenUse (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ k) = 3 := rfl
-- Independent openings overlap; `look` serialises them.
-- Scalar use adds a dependency only to the scalar multiplication.
example (v₁ v₂ : F) : (Sched.output (Std.timed F) (revealBoth (fs := Std F) (D := .timed) ⟪v₁⟫ ⟪v₂⟫)).2.time = 1 := rfl
example (v₁ v₂ : F) :
    (Sched.output (Std.timed F) (revealBothLook (fs := Std F) (D := .timed) ⟪v₁⟫ ⟪v₂⟫)).2.time = 2 := rfl
example (v₁ v₂ x : F) :
    (Sched.output (Std.timed F) (revealUseReveal (fs := Std F) (D := .timed) ⟪v₁⟫ ⟪v₂⟫ ⟪x⟫)).1.time = 1 := rfl
-- Check the arithmetic output of the timed run.
example (a b c d : F) :
    (Sched.output (Std.timed F) (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫)).val = a * b * (c * d) := rfl
end

/-! ## Models of a compound operation -/

namespace MulAdd
inductive Op where | mulAdd
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [.share F, .share F, .share F]
  cod _ := .share F
def eval (F : Type) [Add F] [Mul F] : Model (ops F) .ideal Id :=
  .silent fun ⟨.mulAdd, (a, b, c, ())⟩ => a * b + c
/-- Input profile with multiplication latency from `a` and `b`,
and zero latency from `c`; also take the maximum with the current clock. -/
def profiled (F : Type) [Add F] [Mul F] (p : Price) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.mulAdd, (a, b, c, ())⟩ =>
      ((⟨a.val * b.val + c.val, max (a.time + p.delay) (max (b.time + p.delay) (max c.time s.clock))⟩, ()),
        s.pay p.comm)⟩
end MulAdd

section Profiles
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

/-- Return a share of `a·b + c`. -/
abbrev MulAdd : Functionality := .ofEval (MulAdd.ops F) (MulAdd.eval F)

/-- Multiply `a` and `b`, then add `c`.
Only the addition depends on `c`. -/
def mulAddImpl {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b c : D.share F) :
    Prog fs.ops D (D.share F) := do
  let p ← mul a b
  add p c

/-- Realise `MulAdd` with a fixed view of one multiplication and one addition. -/
program mulAddReal : Realization (MulAdd F) (Std F) where
  impl D r := mulAddImpl F r.args.1 r.args.2.1 r.args.2.2.1
  Sim _ := pure [⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.lin F .add, ((), (), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, a, b, c, ⟨⟩⟩ := r
    simp only [mulAddImpl, mul, add, weft, Functionality.ofEval_model, MulAdd.eval]
    rfl

/-- Supply `c` from a separate multiplication `x·y`. -/
def caller {fs : Hybrid} {D : Domain} [Has (MulAdd F) fs] [Has (Mult F) fs] (a b x y : D.share F) :
    Prog fs.ops D (D.share F) := do
  let c ← mul x y
  Prog.op (F := MulAdd F) ⟨.mulAdd, (a, b, c, ())⟩
/-- Inline `mulAddImpl` into the caller. -/
def callerInlined {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b x y : D.share F) :
    Prog fs.ops D (D.share F) := do
  let c ← mul x y
  mulAddImpl F a b c

/-- Compound multiply-add with linear operations and multiplication. -/
abbrev Hyb : Hybrid := [MulAdd F, Lin F, Mult F]

/-- Fixed-price, profiled and implementation-derived models of the same hybrid. -/
abbrev atomicMPC : MPC := [(MulAdd F).priced ⟨1, 2⟩, (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]
abbrev profiledMPC : MPC := [MPC.entry (MulAdd F) (MulAdd.profiled F ⟨1, 2⟩), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]
noncomputable abbrev derivedMPC : MPC := [MPC.derived (Std.mpc F) (mulAddReal F), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]

-- The fixed-price model waits for `c` at round 1,
-- then charges another multiplication round.
example (a b x y : F) : delayOn (atomicMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 2 := rfl
-- The profile overlaps `a·b` with the computation of `c`.
example (a b x y : F) : delayOn (profiledMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- Running the implementation also finishes at round 1.
example (a b x y : F) : delayOn (derivedMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- Inlining agrees with the profiled and derived models on this caller.
example (a b x y : F) : delayOn (Std.timed F) (callerInlined F (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl

/-- Realise the hybrid over `Std F` for the timing composition theorem below. -/
noncomputable def mulAddOverStd : Realizations (Hyb F) (Std F) :=
  .cons (mulAddReal F) (Realizations.incl [Lin F, Mult F] (Std F))
example (a b x y : F) :
    delayOn ((mulAddOverStd F).timed (Std.timed F)) (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫)
      = delayOn (Std.timed F) (Prog.handle ((mulAddOverStd F).impl .timed)
          (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫)) :=
  Realizations.delayOn_timed _ _ _

end Profiles

end Weft.Examples.Timing
