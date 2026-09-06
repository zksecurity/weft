import Weft
import Examples.Basic
import Examples.Privacy
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# From the AES-hybrid to a plain program

1. Write a protocol in the **AES-hybrid**: a hybrid that lists an AES
   functionality alongside the arithmetic black box, so the protocol may
   call `enc`, whose only meaning is the functionality's model.
2. Give a **program for AES** over the black box alone and prove it
   realises the AES functionality.
3. **Instantiate**: inline that program into the protocol.  The result is a
   program over the black box alone, and its correctness, cost and privacy
   are what the composition theorems say.

The block cipher here is a toy, `(m + k)³`, so that the realisation proof
closes; real AES changes the size of the program, not the shape of any step.

The UC shape comes last: the protocol is itself a functionality, `CBC`,
realised over the AES-hybrid once, against the AES *specification*; any
realisation of AES over the black box composes in with `Realization.comp`.
-/
namespace Weft.Examples.Aes
open Weft.Examples.Basic

/-! ### The AES functionality: one operation, two share operands, a share response, nothing declared -/

namespace AesF
inductive Op where | enc
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := .share F ⊗ .share F
  cod _ := .share F
def eval (F : Type) (aes : F → F → F) : Model (ops F) .ideal Id := .silent fun ⟨.enc, (k, m)⟩ => aes k m
end AesF

/-- The AES functionality for a block function `aes`: computes `aes k m`, leaks nothing. -/
abbrev AES (F : Type) (aes : F → F → F) : Functionality := .ofEval (AesF.ops F) (AesF.eval F aes)

section
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- The specification of the (toy) block cipher. -/
def toyAes (k m : F) : F := (m + k) * (m + k) * (m + k)

/-- Call the AES functionality. -/
def enc (aes : F → F → F) [Has (AES F aes) fs] (k m : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := AES F aes) ⟨.enc, (k, m)⟩

/-! ### Step 1: the protocol, in the AES-hybrid -/

/-- CBC encryption of two blocks, written against AES *and* the black box.
It knows nothing about how AES is realised. -/
def cbc2 (aes : F → F → F) [Has (AES F aes) fs] [Has (Lin F) fs] (k iv m₁ m₂ : D.share F) :
    Prog fs.ops D (D.share F × D.share F) := do
  let x₁ ← add iv m₁
  let c₁ ← enc aes k x₁
  let x₂ ← add c₁ m₂
  let c₂ ← enc aes k x₂
  pure (c₁, c₂)

/-! ### Step 2: a program for AES over the black box -/

/-- The toy cipher with the arithmetic black box only (polymorphic in the
domain, so the same definition is timed below). -/
def toyAesProg [Has (Lin F) fs] [Has (Mult F) fs] (k m : D.share F) : Prog fs.ops D (D.share F) := do
  let t ← add m k
  let t2 ← mul t t
  mul t2 t
end

section
variable (F : Type) [Field F] [Inhabited F]

/-- The AES-hybrid: an MPC that offers `enc` alongside the arithmetic black box. -/
abbrev AesHybrid : Hybrid := [AES F (toyAes), Lin F, Mult F, Reveal F]

/-- **The obligation**: the program computes the specification, and its view
is one linear record and two multiplication records, which the simulator
produces from the AES functionality's event. -/
program aesByProgram : Realization (AES F toyAes) (Std F) where
  impl D r := toyAesProg r.args.1 r.args.2
  Sim _ := pure [⟨Std.lin F .add, ((), ()), (), ()⟩, ⟨Std.mult F, ((), ()), (), ()⟩, ⟨Std.mult F, ((), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, k, m⟩ := r
    simp only [toyAesProg, toyAes, add, mul, weft, Functionality.ofEval_model, AesF.eval]
    rfl

/-! ### Step 3: instantiate, and what transfers -/

/-- Realisations of every component of the AES-hybrid over the black box:
AES by the program, the rest by themselves. -/
noncomputable def hybridOverStd : Realizations (AesHybrid F) (Std F) :=
  .cons (aesByProgram F) (Realizations.incl [Lin F, Mult F, Reveal F] (Std F))

/-- The instantiated protocol: a program over `Std F`, no AES left. -/
noncomputable def cbc2Plain (k iv m₁ m₂ : F) : Prog (Std F).ops .ideal (F × F) :=
  Prog.handle ((hybridOverStd F).impl .ideal) (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)

-- Correctness in the hybrid, against the AES *specification*.
example (k iv m₁ m₂ : F) :
    output (AesHybrid F).eval (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)
      = (toyAes k (iv + m₁), toyAes k (toyAes k (iv + m₁) + m₂)) := rfl
-- ...and after instantiation, the same values, by the composition theorem.
omit [Inhabited F] in
theorem cbc2Plain_output (k iv m₁ m₂ : F) :
    Prod.fst <$> dist (Std F).model (cbc2Plain F k iv m₁ m₂)
      = Prod.fst <$> dist (AesHybrid F).model (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂) :=
  output_transport (hybridOverStd F) _ (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) _)

-- The view in the hybrid: nothing but the operations.
example (k iv m₁ m₂ : F) :
    view (AesHybrid F).eval (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)
      = [⟨⟨1, .add⟩, ((), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), ()), (), ()⟩, ⟨⟨1, .add⟩, ((), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), ()), (), ()⟩] := rfl

-- Delay, in the timed domain: in the hybrid `enc` is one operation of latency 1 (CBC of two
-- blocks is 2); after instantiation `enc` costs what the program costs, two dependent
-- multiplications (so 4).
abbrev aesMPC : MPC := [(AES F toyAes).priced ⟨1, 10⟩, (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]
abbrev stdMPC : MPC := Std.mpc F
/-- The exact instantiation of `enc`: run the program. -/
noncomputable abbrev aesDerived : MPC :=
  [MPC.derived (stdMPC F) (aesByProgram F), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]
end

-- Closed instances over `𝔽₇`, evaluated by the kernel.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
/-- CBC on the instance, against an MPC. -/
abbrev cbcAt (M : MPC) [Has (AES (ZMod 7) toyAes) M.hybrid] [Has (Lin (ZMod 7)) M.hybrid] :
    Prog M.hybrid.ops .timed (Timed (ZMod 7) × Timed (ZMod 7)) :=
  cbc2 (F := ZMod 7) (fs := M.hybrid) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫
-- Rounds: 2 with `enc` priced at one round; 4 with `enc` run as its program, or inlined.
example : (Sched.output (aesMPC (ZMod 7)).timed (cbcAt (aesMPC (ZMod 7)))).2.time = 2 := by decide +kernel
example : (Sched.output (aesDerived (ZMod 7)).timed (cbcAt (aesDerived (ZMod 7)))).2.time = 4 := by decide +kernel
example : (Sched.output (stdMPC (ZMod 7)).timed (Prog.handle ((hybridOverStd (ZMod 7)).impl .timed)
    (cbc2 (F := ZMod 7) (fs := AesHybrid (ZMod 7)) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫))).2.time = 4 := by
  decide +kernel
-- Communication: ten units per AES call at that price; four per AES call derived or inlined.
example : commOn (aesMPC (ZMod 7)).timed (cbcAt (aesMPC (ZMod 7))) = 20 := by decide +kernel
example : commOn (aesDerived (ZMod 7)).timed (cbcAt (aesDerived (ZMod 7))) = 8 := by decide +kernel
example : commOn (stdMPC (ZMod 7)).timed (Prog.handle ((hybridOverStd (ZMod 7)).impl .timed)
    (cbc2 (F := ZMod 7) (fs := AesHybrid (ZMod 7)) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫)) = 8 := by decide +kernel

section
variable (F : Type) [Field F] [Inhabited F]
-- ...and that is a theorem, for every caller, not an observation.
example (k iv m₁ m₂ : F) :
    commOn ((hybridOverStd F).timed (Std.timed F)) (cbc2 (fs := AesHybrid F) (D := .timed) toyAes ⟪k⟫ ⟪iv⟫ ⟪m₁⟫ ⟪m₂⟫)
      = commOn (Std.timed F) (Prog.handle ((hybridOverStd F).impl .timed)
          (cbc2 (fs := AesHybrid F) (D := .timed) toyAes ⟪k⟫ ⟪iv⟫ ⟪m₁⟫ ⟪m₂⟫)) :=
  Realizations.commOn_timed _ _ _

/-! ### The UC shape: prove the protocol against *its own* specification first -/

/-- The specification of the protocol, stated through the AES specification. -/
abbrev CBC : Functionality :=
  .ofEval ⟨Unit, fun _ => .share F ⊗ .share F ⊗ .share F ⊗ .share F, fun _ => .prod (.share F) (.share F), fun _ => Unit⟩
    ⟨fun r => pure ((toyAes r.args.1 (r.args.2.1 + r.args.2.2.1),
      toyAes r.args.1 (toyAes r.args.1 (r.args.2.1 + r.args.2.2.1) + r.args.2.2.2)), ())⟩

/-- **Done first, once, against the AES specification only.**  The simulator
replays the four silent records. -/
program cbcOverHybrid : Realization (CBC F) (AesHybrid F) where
  impl D r := cbc2 toyAes r.args.1 r.args.2.1 r.args.2.2.1 r.args.2.2.2
  Sim _ := pure [⟨⟨1, .add⟩, ((), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), ()), (), ()⟩, ⟨⟨1, .add⟩, ((), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, k, iv, m₁, m₂⟩ := r
    simp only [cbc2, enc, add, weft, Functionality.ofEval_model, AesF.eval]
    rfl

/-- **Done later, by composition**: plug in the realisation of AES over the
black box.  A realisation of `CBC` over `Std F` alone, with no new proof. -/
noncomputable def cbcOverStd : Realization (CBC F) (Std F) :=
  (cbcOverHybrid F).comp (hybridOverStd F)

-- The composed implementation is literally the instantiated program.
example (k iv m₁ m₂ : F) : (cbcOverStd F).impl .ideal ⟨(), (k, iv, m₁, m₂)⟩ = cbc2Plain F k iv m₁ m₂ := rfl

-- Its precondition is discharged: the hybrid realisation has none, and the caller is valid
-- for the trivial preconditions of the black box.
omit [Inhabited F] in
theorem cbcOverStd_pre (r : Req (CBC F).ops .ideal) : (cbcOverStd F).Pre r :=
  ⟨trivial, Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) _⟩
end

end Weft.Examples.Aes
