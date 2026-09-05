import Weft
import Examples.Basic

/-!
# Delay by dependency tracking: examples and timing profiles

No `∥` anywhere: sequential `do`-code gets the parallel count, because
delay is computed from data dependencies in the timed domain.

The second part is about composition.  An abstract operation is a
functionality, behaviour only; what it costs is decided by the cost model
that instantiates it.  A single latency serialises its whole
implementation behind all of its inputs; a *timing profile* (the longest
path from each input to the output) is exact for a straight-line
implementation in isolation but not in general (report, Issue 10): the
reveal and control clocks are global state, so an inlined callee that
reveals waits on every earlier reveal of the caller, which no per-input
profile can know.  The exact instantiation is to *run the implementation*
in the target's cost model (`Realization.timed`); the hybrid then costs
what the inlined program costs, as a theorem (`Realizations.delayOn_timed`),
and atomic and profiled models are approximations of it.
-/
namespace Weft.Examples.Timing
open Weft.Examples.Basic

section Programs
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- Written sequentially; `ab` and `cd` do not depend on each other. -/
def mul4seq [Has (Mult F) fs] (a b c d : D.sh F) : Prog fs.ops D (D.sh F) := do
  let ab ← mul a b
  let cd ← mul c d
  mul ab cd

/-- A genuinely sequential chain. -/
def chain3 [Has (Mult F) fs] (a b c d : D.sh F) : Prog fs.ops D (D.sh F) := do
  let x ← mul a b
  let y ← mul x c
  mul y d

/-- Reveal, compute in the clear, insert back: the reveal clock carries the
time into the clear computation and back in through `const`. -/
def revealThenUse [Has (Lin F) fs] [Has (Mult F) fs] [Has (Reveal F) fs] (a b c : D.sh F) (k : F) :
    Prog fs.ops D (D.sh F) := do
  let p ← mul a b
  let v ← reveal p
  let t ← const (v * k)
  mul t c
end Programs

section
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

-- Two rounds, not three: `ab` and `cd` are independent, and the pass sees it.
example (a b c d : F) : delayOn (Std.timed F) (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 2 := rfl
-- The genuinely sequential chain is still three.
example (a b c d : F) : delayOn (Std.timed F) (chain3 (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 3 := rfl
-- Reveal at 2, clear computation, `const` at 2, multiplication at 3.
example (a b c k : F) : delayOn (Std.timed F) (revealThenUse (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ k) = 3 := rfl
-- Values are unchanged: the timed model computes the same thing.
example (a b c d : F) :
    (Sched.output (Std.timed F) (mul4seq (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫)).val = a * b * (c * d) := rfl
end

/-! ## An abstract operation, and how a cost model instantiates it -/

namespace MulAdd
inductive Op where | mulAdd
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F, F, F]
  cod _ := .share F
def eval (F : Type) [Add F] [Mul F] : Model (ops F) .ideal Id :=
  .silent fun ⟨.mulAdd, (a, b, c, ())⟩ => a * b + c
/-- The *profiled* instantiation, a hand-written timed model of the interface:
`d_a = d_b = delay`, `d_c = 0`.  (The atomic one is the generic model at a price.) -/
def profiled (F : Type) [Add F] [Mul F] (p : Price) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.mulAdd, (a, b, c, ())⟩ =>
      ((⟨a.val * b.val + c.val, max (a.time + p.delay) (max (b.time + p.delay) (max c.time s.clock))⟩, ()),
        s.pay p.comm)⟩
end MulAdd

section Profiles
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

/-- The abstract operation `mulAdd a b c = a·b + c`: one functionality,
behaviour only.  What it costs is the cost model's business. -/
abbrev MulAdd : Functionality := .ofEval (MulAdd.ops F) (MulAdd.eval F)

/-- Its implementation over the black box: `c` is only needed after the multiplication. -/
def mulAddImpl {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b c : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let p ← mul a b
  add p c

/-- ...and the certificate that it realises `MulAdd`. -/
program mulAddReal : Realization (MulAdd F) (Std F) where
  impl D r := mulAddImpl F r.args.1 r.args.2.1 r.args.2.2.1
  Sim _ := pure [⟨Std.mult F, (), ()⟩, ⟨Std.lin F .add, (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, a, b, c, ⟨⟩⟩ := r
    simp only [mulAddImpl, mul, add, weft, Functionality.ofEval_model, MulAdd.eval]
    rfl

/-- A caller in which `c` arrives late: `c = x·y` is ready at round 1. -/
def caller {fs : Hybrid} {D : Domain} [Has (MulAdd F) fs] [Has (Mult F) fs] (a b x y : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let c ← mul x y
  Prog.op (F := MulAdd F) ⟨.mulAdd, (a, b, c, ())⟩
/-- The same caller with the operation inlined. -/
def callerInlined {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b x y : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let c ← mul x y
  mulAddImpl F a b c

/-- The hybrid the caller is written in. -/
abbrev Hyb : Hybrid := [MulAdd F, Lin F, Mult F]

/-- Three cost models for the one hybrid: `mulAdd` atomic (a price), profiled
(a hand-written timed model), and instantiated by running its
implementation over the black box. -/
abbrev atomicMPC : MPC := [(MulAdd F).priced ⟨1, 2⟩, (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]
abbrev profiledMPC : MPC := [MPC.entry (MulAdd F) (MulAdd.profiled F ⟨1, 2⟩), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]
noncomputable abbrev derivedMPC : MPC := [MPC.derived (Std.mpc F) (mulAddReal F), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩]

-- Atomic: mulAdd waits for c (round 1), then 1 round: 2.  Inlined: p = a·b at round 1
-- in parallel with c, then a free add: 1.  The atomic model over-approximates...
example (a b x y : F) : delayOn (atomicMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 2 := rfl
-- ...the profile is exact here...
example (a b x y : F) : delayOn (profiledMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- ...the derived instantiation is exact by construction...
example (a b x y : F) : delayOn (derivedMPC F).timed (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- ...and all agree with the inlined program on this caller.
example (a b x y : F) : delayOn (Std.timed F) (callerInlined F (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl

/-- **Delay composes exactly** under the derived instantiation: this is
`Realizations.delayOn_timed`, for every caller, not a check on one. -/
noncomputable def mulAddOverStd : Realizations (Hyb F) (Std F) :=
  .cons (mulAddReal F) (Realizations.incl [Lin F, Mult F] (Std F))
example (a b x y : F) :
    delayOn ((mulAddOverStd F).timed (Std.timed F)) (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫)
      = delayOn (Std.timed F) (Prog.handle ((mulAddOverStd F).impl .timed)
          (caller F (fs := Hyb F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫)) :=
  Realizations.delayOn_timed _ _ _

end Profiles

end Weft.Examples.Timing
