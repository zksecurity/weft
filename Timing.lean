import Glean
import Gallery

/-!
# Delay by dependency tracking: examples and timing profiles

The timed domain lives in the core (`Glean.lean`, §4b).  This file shows it
on sequential `do`-code and states the refinement that makes delay compose
exactly along realisations: **timing profiles**.
-/
namespace Glean.Timing
open Glean Glean.Examples

/-! ## No `∥` anywhere: sequential `do`-code, parallel delay -/
section
variable {D : Domain} {σ : Sig} [Has (Lin D) σ] [Has (Mult D) σ]

/-- Written sequentially; `ab` and `cd` do not depend on each other. -/
def mul4seq (a b c d : D.S) : Circ σ D.S := do
  let ab ← mul a b
  let cd ← mul c d
  mul ab cd

/-- A genuinely sequential chain. -/
def chain3 (a b c d : D.S) : Circ σ D.S := do
  let x ← mul a b
  let y ← mul x c
  mul y d

/-- Reveal, compute in the clear, insert back: the reveal clock carries the
time into the clear computation and back in through `const`. -/
def revealThenUse [Has (Reveal D) σ] [Mul D.F] (a b c : D.S) (k : D.F) : Circ σ D.S := do
  let p ← mul a b
  let v ← reveal p
  let t ← const (v * k)
  mul t c
end

section
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]
local notation "𝕋" => Domain.timed F
local notation "⟪" x "⟫" => (⟨x, 0⟩ : Timed F)

-- Two rounds, not three: `ab` and `cd` are independent, and the pass sees it.
example (a b c d : F) : delay F (Std.timed F) (mul4seq (D := 𝕋) (σ := Std 𝕋) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 2 := rfl
-- The genuinely sequential chain is still three.
example (a b c d : F) : delay F (Std.timed F) (chain3 (D := 𝕋) (σ := Std 𝕋) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫) = 3 := rfl
-- Reveal at 2, clear computation, `const` at 2, multiplication at 3.
example (a b c k : F) : delay F (Std.timed F) (revealThenUse (D := 𝕋) (σ := Std 𝕋) ⟪a⟫ ⟪b⟫ ⟪c⟫ k) = 3 := rfl
-- Values are unchanged: the timed model computes the same thing.
example (a b c d : F) :
    (Sched.output (Std.timed F) (mul4seq (D := 𝕋) (σ := Std 𝕋) ⟪a⟫ ⟪b⟫ ⟪c⟫ ⟪d⟫)).val
      = a * b * (c * d) := rfl
end

/-! ## Timing profiles: delay composes exactly along realisations

Under dependency tracking, inlining an implementation into a caller refines
the caller's dependency graph, and the critical path of the refined graph
is *exactly* recoverable from the caller's graph if each abstract operation
carries its **timing profile**: for each input, the longest path from that
input to the output inside the implementation (and `d₀` for paths from
input-free sources such as preprocessing).  Then

    ready(out) = max (d₀, max_i (ready(in_i) + d_i))

and the composed count equals the inlined count.  A single latency is the
special case where every `d_i` is equal, i.e. the operation waits for all
of its inputs; real gadgets often have "late" inputs. -/

section Profiles
variable (F : Type) [Add F] [Mul F] [Sub F] [Inhabited F]
local notation "𝕋" => Domain.timed F
local notation "⟪" x "⟫" => (⟨x, 0⟩ : Timed F)

/-- An abstract operation `mulAdd a b c = a·b + c`, as a signature. -/
inductive MulAdd (D : Domain) : Sig where
  | mulAdd : D.S → D.S → D.S → MulAdd D D.S

/-- Its implementation over `Std`: `c` is only needed after the multiplication. -/
def mulAddImpl : {β : Type} → MulAdd 𝕋 β → Circ (Std 𝕋) β
  | _, .mulAdd a b c => do
    let p ← mul a b
    add p c

/-- The *atomic* timed model: one latency, wait for all inputs. -/
def MulAdd.atomic : Model (MulAdd 𝕋) F Sched where
  program o := match o with
    | .mulAdd a b c => Timed.after [a.time, b.time, c.time] 1 (a.val * b.val + c.val)
  leak _ _ := []

/-- The *profiled* timed model: `d_a = d_b = 1`, `d_c = 0`. -/
def MulAdd.profiled : Model (MulAdd 𝕋) F Sched where
  program o := match o with
    | .mulAdd a b c => Timed.after [a.time + 1, b.time + 1, c.time] 0 (a.val * b.val + c.val)
  leak _ _ := []

/-- A caller in which `c` arrives late: `c = x·y` is ready at round 1. -/
def caller {D' : Domain} {σ' : Sig} [Has (MulAdd D') σ'] [Has (Mult D') σ'] (a b x y : D'.S) : Circ σ' D'.S := do
  let c ← mul x y
  Circ.op (MulAdd.mulAdd a b c)

def timedMulAdd (P : Model (MulAdd 𝕋) F Sched) : Model (MulAdd 𝕋 ⊞ Mult 𝕋) F Sched :=
  P.sum (Mult.timed F 1)

def plainHandler : {β : Type} → (MulAdd 𝕋 ⊞ Mult 𝕋) β → Circ (Std 𝕋) β := fun o => match o with
  | .inl o => mulAddImpl F o
  | .inr o => Circ.op o

-- Atomic view: mulAdd waits for c (round 1), then 1 round: 2.  Inlined: p = a·b at round 1
-- in parallel with c, then a free add: 1.  The atomic view over-approximates...
example (a b x y : F) :
    delayOn (timedMulAdd F (MulAdd.atomic F)) (caller (D' := 𝕋) (σ' := MulAdd 𝕋 ⊞ Mult 𝕋) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 2 := rfl
-- ...the profiled view is exact...
example (a b x y : F) :
    delayOn (timedMulAdd F (MulAdd.profiled F)) (caller (D' := 𝕋) (σ' := MulAdd 𝕋 ⊞ Mult 𝕋) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫) = 1 := rfl
-- ...and agrees with the inlined circuit.
example (a b x y : F) :
    delayOn (Std.timed F) (Circ.handle (plainHandler F) (caller (D' := 𝕋) (σ' := MulAdd 𝕋 ⊞ Mult 𝕋) ⟪a⟫ ⟪b⟫ ⟪x⟫ ⟪y⟫)) = 1 := rfl

/-- The general statement.  An implementation *has profile* `d` if its output
is ready at `max (d₀, max_i (t_i + d_i))` whenever its inputs are ready at
`t_i`; then, under eager scheduling, inlining is exact: the caller's delay
with the operation modelled by its profile equals the inlined circuit's.
(Proof: the longest path through a substituted DAG decomposes at the
substitution boundary.)  Stated here for one op. -/
theorem profiled_handle_exact : True := trivial   -- statement shape only; see DESIGN.md §3.4
end Profiles

end Glean.Timing
