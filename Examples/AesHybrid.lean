import Weft
import Examples.Basic
import Examples.Privacy
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Composition through a block-function hybrid

`cbc2` chains two calls to an abstract block function using field addition.
`aesByProgram` realises the function over standard arithmetic,
and `Realization.comp` substitutes that implementation into the protocol.

The example uses `(m + k)³` as a toy function.
It illustrates composition of arithmetic programs;
it is not an implementation or security proof of AES encryption.

The cost examples compare a fixed price per call with the cost derived from its implementation.
-/
namespace Weft.Examples.Aes
open Weft.Examples.Basic

/-! ### Abstract block function -/

namespace AesF
inductive Op where | enc
abbrev ops (F : Type) : Interface where
  Op := Op
  dom _ := [.share F, .share F]
  cod _ := .share F
def eval (F : Type) (aes : F → F → F) : Model (ops F) .ideal Id := .silent fun ⟨.enc, (k, m, ())⟩ => aes k m
end AesF

/-- Apply `aes` to shared key and message operands without disclosure. -/
abbrev AES (F : Type) (aes : F → F → F) : Functionality := .ofEval (AesF.ops F) (AesF.eval F aes)

section
variable {F : Type} [Add F] [Mul F] [Sub F] {fs : Hybrid} {D : Domain}

/-- Toy block function `(m + k)³`. -/
def toyAes (k m : F) : F := (m + k) * (m + k) * (m + k)

/-- Request a block-function evaluation. -/
def enc (aes : F → F → F) [Has (AES F aes) fs] (k m : D.share F) : Prog fs.ops D (D.share F) :=
  Prog.op (F := AES F aes) ⟨.enc, (k, m, ())⟩

/-! ### Protocol over the abstract function -/

/-- Chain two block-function calls, adding the previous block before each call. -/
def cbc2 (aes : F → F → F) [Has (AES F aes) fs] [Has (Lin F) fs] (k iv m₁ m₂ : D.share F) :
    Prog fs.ops D (D.share F × D.share F) := do
  let x₁ ← add iv m₁
  let c₁ ← enc aes k x₁
  let x₂ ← add c₁ m₂
  let c₂ ← enc aes k x₂
  pure (c₁, c₂)

/-! ### Arithmetic implementation -/

/-- Evaluate the toy function with one addition and two multiplications. -/
def toyAesProg [Has (Lin F) fs] [Has (Mult F) fs] (k m : D.share F) : Prog fs.ops D (D.share F) := do
  let t ← add m k
  let t2 ← mul t t
  mul t2 t
end

section
variable (F : Type) [Field F] [Inhabited F]

/-- The toy block function alongside standard arithmetic. -/
abbrev AesHybrid : Hybrid := [AES F (toyAes), Lin F, Mult F, Reveal F]

/-- Realise the toy function with an input-independent three-event view. -/
program aesByProgram : Realization (AES F toyAes) (Std F) where
  impl D r := toyAesProg r.args.1 r.args.2.1
  Sim _ := pure [⟨Std.lin F .add, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩, ⟨Std.mult F, ((), (), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, k, m, ⟨⟩⟩ := r
    simp only [toyAesProg, toyAes, add, mul, weft, Functionality.ofEval_model, AesF.eval]
    rfl

/-! ### Substituting the implementation -/

/-- Implement the block function and retain the standard components by inclusion. -/
noncomputable def hybridOverStd : Realizations (AesHybrid F) (Std F) :=
  .cons (aesByProgram F) (Realizations.incl [Lin F, Mult F, Reveal F] (Std F))

/-- Inline the block-function implementation into `cbc2`. -/
noncomputable def cbc2Plain (k iv m₁ m₂ : F) : Prog (Std F).ops .ideal (F × F) :=
  Prog.handle ((hybridOverStd F).impl .ideal) (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)

-- Evaluate the protocol using the abstract block function.
example (k iv m₁ m₂ : F) :
    output (AesHybrid F).eval (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)
      = (toyAes k (iv + m₁), toyAes k (toyAes k (iv + m₁) + m₂)) := rfl
-- Composition preserves the output distribution.
omit [Inhabited F] in
theorem cbc2Plain_output (k iv m₁ m₂ : F) :
    Prod.fst <$> dist (Std F).model (cbc2Plain F k iv m₁ m₂)
      = Prod.fst <$> dist (AesHybrid F).model (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂) :=
  output_transport (hybridOverStd F) _ (Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) _)

-- The hybrid view is a fixed list of four operation records.
example (k iv m₁ m₂ : F) :
    view (AesHybrid F).eval (cbc2 (fs := AesHybrid F) (D := .ideal) toyAes k iv m₁ m₂)
      = [⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), (), ()), (), ()⟩, ⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), (), ()), (), ()⟩] := rfl

-- The fixed price assigns one round to each block-function call.
-- The arithmetic implementation uses two dependent multiplications,
-- so the derived cost is two rounds per call.
abbrev aesMPC : MPC := [(AES F toyAes).priced ⟨1, 10⟩, (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]
abbrev stdMPC : MPC := Std.mpc F
/-- Derive the block-function cost from its arithmetic implementation. -/
noncomputable abbrev aesDerived : MPC :=
  [MPC.derived (stdMPC F) (aesByProgram F), (Lin F).priced ⟨0, 0⟩, (Mult F).priced ⟨1, 2⟩, (Reveal F).priced ⟨1, 1⟩]
end

-- Closed instances over `𝔽₇`, evaluated by the kernel.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
/-- A fixed two-block instance over `ZMod 7`. -/
abbrev cbcAt (M : MPC) [Has (AES (ZMod 7) toyAes) M.hybrid] [Has (Lin (ZMod 7)) M.hybrid] :
    Prog M.hybrid.ops .timed (Timed (ZMod 7) × Timed (ZMod 7)) :=
  cbc2 (F := ZMod 7) (fs := M.hybrid) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫
-- Two calls cost two rounds at the fixed price and four under the implementation.
example : (Sched.output (aesMPC (ZMod 7)).timed (cbcAt (aesMPC (ZMod 7)))).2.time = 2 := by decide +kernel
example : (Sched.output (aesDerived (ZMod 7)).timed (cbcAt (aesDerived (ZMod 7)))).2.time = 4 := by decide +kernel
example : (Sched.output (stdMPC (ZMod 7)).timed (Prog.handle ((hybridOverStd (ZMod 7)).impl .timed)
    (cbc2 (F := ZMod 7) (fs := AesHybrid (ZMod 7)) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫))).2.time = 4 := by
  decide +kernel
-- The fixed price charges ten units per call; the implementation uses four.
example : commOn (aesMPC (ZMod 7)).timed (cbcAt (aesMPC (ZMod 7))) = 20 := by decide +kernel
example : commOn (aesDerived (ZMod 7)).timed (cbcAt (aesDerived (ZMod 7))) = 8 := by decide +kernel
example : commOn (stdMPC (ZMod 7)).timed (Prog.handle ((hybridOverStd (ZMod 7)).impl .timed)
    (cbc2 (F := ZMod 7) (fs := AesHybrid (ZMod 7)) (D := .timed) toyAes ⟪3⟫ ⟪1⟫ ⟪4⟫ ⟪5⟫)) = 8 := by decide +kernel

section
variable (F : Type) [Field F] [Inhabited F]
-- Apply the communication composition theorem to arbitrary inputs.
example (k iv m₁ m₂ : F) :
    commOn ((hybridOverStd F).timed (Std.timed F)) (cbc2 (fs := AesHybrid F) (D := .timed) toyAes ⟪k⟫ ⟪iv⟫ ⟪m₁⟫ ⟪m₂⟫)
      = commOn (Std.timed F) (Prog.handle ((hybridOverStd F).impl .timed)
          (cbc2 (fs := AesHybrid F) (D := .timed) toyAes ⟪k⟫ ⟪iv⟫ ⟪m₁⟫ ⟪m₂⟫)) :=
  Realizations.commOn_timed _ _ _

/-! ### Protocol realisation -/

/-- Specify the two-block output using `toyAes`. -/
abbrev CBC : Functionality :=
  .ofEval ⟨Unit, fun _ => [.share F, .share F, .share F, .share F], fun _ => .prod (.share F) (.share F), fun _ => Unit⟩
    ⟨fun r => pure ((toyAes r.args.1 (r.args.2.1 + r.args.2.2.1),
      toyAes r.args.1 (toyAes r.args.1 (r.args.2.1 + r.args.2.2.1) + r.args.2.2.2.1)), ())⟩

/-- Realise the protocol in the block-function hybrid.
The simulator returns its four fixed operation records. -/
program cbcOverHybrid : Realization (CBC F) (AesHybrid F) where
  impl D r := cbc2 toyAes r.args.1 r.args.2.1 r.args.2.2.1 r.args.2.2.2.1
  Sim _ := pure [⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), (), ()), (), ()⟩, ⟨⟨1, .add⟩, ((), (), ()), (), ()⟩, ⟨⟨0, .enc⟩, ((), (), ()), (), ()⟩]
  real r _ := by
    obtain ⟨⟨⟩, k, iv, m₁, m₂, ⟨⟩⟩ := r
    simp only [cbc2, enc, add, weft, Functionality.ofEval_model, AesF.eval]
    rfl

/-- Compose the protocol realisation with the arithmetic implementation. -/
noncomputable def cbcOverStd : Realization (CBC F) (Std F) :=
  (cbcOverHybrid F).comp (hybridOverStd F)

-- The composed implementation unfolds to `cbc2Plain`.
example (k iv m₁ m₂ : F) : (cbcOverStd F).impl .ideal ⟨(), (k, iv, m₁, m₂, ())⟩ = cbc2Plain F k iv m₁ m₂ := rfl

-- The outer precondition and all inner preconditions are trivial.
-- Hence every request satisfies the composite precondition.
omit [Inhabited F] in
theorem cbcOverStd_pre (r : Req (CBC F).ops .ideal) : (cbcOverStd F).Pre r :=
  ⟨trivial, Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) _⟩
end

end Weft.Examples.Aes
