import Weft
import Examples.Basic

/-!
# Delay by dependency tracking: examples and timing profiles

No `∥` anywhere: sequential `do`-code gets the parallel count, because
delay is computed from data dependencies in the timed domain.

The second part is about composition.  Under dependency tracking an
abstract operation should not be modelled by a single latency, which
serialises its whole implementation behind all of its inputs; a *timing
profile* (the longest path from each input to the output) is exact for a
straight-line implementation in isolation.  It is **not** exact in general
(report, Issue 10): the reveal and control clocks are global state, so an
inlined callee that reveals waits on every earlier reveal of the caller,
which no per-input profile can know.  Profiles are a conservative bound
whose clock-aware statement is future work; the example below shows the
straight-line case where atomic over-counts and the profile is exact.
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

/-! ## Timing profiles: exact for a straight-line callee in isolation -/

namespace MulAdd
inductive Op where | mulAdd
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [F, F, F]
  cod _ := .share F
def eval (F : Type) [Add F] [Mul F] : Model (ops F) .ideal Id :=
  .silent fun ⟨.mulAdd, (a, b, c, ())⟩ => a * b + c
/-- The *atomic* timed model: one latency, wait for all inputs. -/
def atomic (F : Type) [Add F] [Mul F] (_ : Op → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.mulAdd, (a, b, c, ())⟩ => ((⟨a.val * b.val + c.val, max a.time (max b.time (max c.time s.clock)) + 1⟩, ()), s)⟩
/-- The *profiled* timed model: `d_a = d_b = 1`, `d_c = 0`. -/
def profiled (F : Type) [Add F] [Mul F] (_ : Op → Nat) : Model (ops F) .timed Sched :=
  ⟨fun r s => match r with
    | ⟨.mulAdd, (a, b, c, ())⟩ => ((⟨a.val * b.val + c.val, max (a.time + 1) (max (b.time + 1) (max c.time s.clock))⟩, ()), s)⟩
end MulAdd

section Profiles
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]

/-- The abstract operation `mulAdd a b c = a·b + c`, timed atomically... -/
abbrev MulAddAtomic : Functionality := .ofEval (MulAdd.ops F) (MulAdd.eval F) (MulAdd.atomic F)
/-- ...and by its profile. -/
abbrev MulAddProfiled : Functionality := .ofEval (MulAdd.ops F) (MulAdd.eval F) (MulAdd.profiled F)

/-- Its implementation over the black box: `c` is only needed after the multiplication. -/
def mulAddImpl {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b c : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let p ← mul a b
  add p c

/-- A caller in which `c` arrives late: `c = x·y` is ready at round 1.  (One
caller per abstract functionality, since the two are different
functionalities under different names.) -/
def callerA {fs : Hybrid} {D : Domain} [Has (MulAddAtomic F) fs] [Has (Mult F) fs] (a b x y : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let c ← mul x y
  Prog.op (F := MulAddAtomic F) ⟨.mulAdd, (a, b, c, ())⟩
def callerP {fs : Hybrid} {D : Domain} [Has (MulAddProfiled F) fs] [Has (Mult F) fs] (a b x y : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let c ← mul x y
  Prog.op (F := MulAddProfiled F) ⟨.mulAdd, (a, b, c, ())⟩
/-- The same caller with the operation inlined. -/
def callerInlined {fs : Hybrid} {D : Domain} [Has (Lin F) fs] [Has (Mult F) fs] (a b x y : D.sh F) :
    Prog fs.ops D (D.sh F) := do
  let c ← mul x y
  mulAddImpl F a b c

abbrev HybA : Hybrid := [MulAddAtomic F, Lin F, Mult F]
abbrev HybP : Hybrid := [MulAddProfiled F, Lin F, Mult F]
def HybA.timed : Model (HybA F).ops .timed Sched := (HybA F).timed fun o => [1, 0, 1].getD o.1 0
def HybP.timed : Model (HybP F).ops .timed Sched := (HybP F).timed fun o => [1, 0, 1].getD o.1 0

-- Atomic view: mulAdd waits for c (round 1), then 1 round: 2.  Inlined: p = a·b at round 1
-- in parallel with c, then a free add: 1.  The atomic view over-approximates...
example (a b x y : F) : delayOn (HybA.timed F) (callerA F (fs := HybA F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 2 := rfl
-- ...the profiled view is exact here...
example (a b x y : F) : delayOn (HybP.timed F) (callerP F (fs := HybP F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- ...and agrees with the inlined program.
example (a b x y : F) : delayOn (Std.timed F) (callerInlined F (fs := Std F) (D := .timed) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl

end Profiles

end Weft.Examples.Timing
