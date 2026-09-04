import Functionality

/-!
# From the AES-hybrid to a plain circuit

1. Write a protocol in the **AES-hybrid**: its signature is `AesOp ⊞ Std`,
   so it may call an `enc` operation whose only meaning is the AES
   functionality's `program` and `leak`.
2. Give a **circuit for AES** over `Std` alone and prove it realises the
   AES functionality.
3. **Instantiate**: inline that circuit into the protocol.  The result is a
   circuit whose signature is `Std` — the AES operation is gone from the
   hybrid — and its correctness, cost and privacy are what the composition
   theorems say.

The block cipher here is a toy, `(m + k)³`, so that the realisation proof
closes; real AES changes the size of the circuit, not the shape of any step.
-/
namespace Glean
open Glean.Examples

section
variable (F : Type) [Field F]
local notation "𝕀" => Domain.ideal F

/-! ### Step 1: the protocol, in the AES-hybrid -/

/-- The AES-hybrid: an MPC that offers `enc` alongside the arithmetic black box. -/
abbrev AesHybrid : Sig := AesOp 𝕀 ⊞ Std 𝕀

/-- CBC encryption of two blocks, written in the hybrid.  Its type says it
may call `enc`; it says nothing about how `enc` is done. -/
def cbc2Hybrid (k iv m₁ m₂ : F) : Circ (AesHybrid F) (F × F) :=
  cbc2 (D := 𝕀) k iv m₁ m₂

/-! ### Step 2: a circuit for AES over `Std`, and the proof it realises AES -/

/-- The specification of the (toy) block cipher. -/
def toyAes (k m : F) : F := (m + k) * (m + k) * (m + k)

/-- A circuit computing it with the arithmetic black box only (polymorphic
in the domain, so the same definition is timed below). -/
def toyAesCircuitD {D : Domain} (k m : D.S) : Circ (Std D) D.S := do
  let t ← add m k
  let t2 ← mul t t
  mul t2 t
def toyAesCircuit (k m : F) : Circ (Std 𝕀) F := toyAesCircuitD (D := 𝕀) k m

/-- The obligation: program agrees, and the view is one linear record and two
multiplication records, which is what a simulator produces from the AES
functionality's empty leak. -/
theorem toyAes_realizes :
    Realizes (ABB F).kind (AES F (toyAes F)).kind (aesHandler F (toyAesCircuit F))
      (ABB F).model (AES F (toyAes F)).model := by
  refine ⟨fun _ _ => pure [(0, []), (1, []), (1, [])], ?_⟩
  intro β o
  cases o
  simp [dist, aesHandler, toyAesCircuit, toyAesCircuitD, toyAes, add, mul, Circ.op, Has.inj, Model.tagged,
    Model.sum, Std.kind, Std.ideal, AesId, Lin.ideal, Mult.ideal, run, Trace.seq]

/-- The realisation of the AES functionality by that circuit. -/
noncomputable def aesByCircuit : Realization (AES F (toyAes F)) (ABB F) :=
  aesCircuit F (toyAes F) (toyAesCircuit F) (toyAes_realizes F)

/-! ### Step 3: instantiate — the AES operation disappears from the hybrid -/

/-- Inline the AES circuit; keep the black box as it is.  The type is the
whole point: `Circ (Std 𝕀) _`, no `AesOp` left. -/
noncomputable def cbc2Plain (k iv m₁ m₂ : F) : Circ (Std 𝕀) (F × F) :=
  Circ.handle (Realization.sum (aesByCircuit F) (Realization.id (ABB F))).impl
    (cbc2Hybrid F k iv m₁ m₂)

/-! ### What transfers -/

/-- The hybrid functionality: AES by its specification, the black box as usual. -/
noncomputable abbrev AesHyb : Functionality F := (AES F (toyAes F)).sum (ABB F)
/-- Its evaluation model. -/
def hybridEval : Model (AesHybrid F) F Id := (AesId F (toyAes F)).sum (Std.ideal F)

theorem hybridModel_eq : (AesHyb F).model = (hybridEval F).lift PMF :=
  (Model.lift_sum _ _).symm

-- Correctness: the plain circuit computes what the hybrid protocol computed
-- against the AES *specification*.
example (k iv m₁ m₂ : F) :
    output (Std.ideal F) (cbc2Plain F k iv m₁ m₂) = output (hybridEval F) (cbc2Hybrid F k iv m₁ m₂) := rfl
example (k iv m₁ m₂ : F) :
    output (Std.ideal F) (cbc2Plain F k iv m₁ m₂)
      = (toyAes F k (iv + m₁), toyAes F k (toyAes F k (iv + m₁) + m₂)) := rfl

-- Leakage: nothing in the hybrid, nothing after instantiation.
example (k iv m₁ m₂ : F) : leak (hybridEval F) (cbc2Hybrid F k iv m₁ m₂) = [] := rfl
example (k iv m₁ m₂ : F) : leak (Std.ideal F) (cbc2Plain F k iv m₁ m₂) = [] := rfl

-- Privacy: proved once in the hybrid (here by evaluation: silent and deterministic)...
theorem cbc2Hybrid_hiding :
    Hiding ((AesHyb F).model.tagged (AesHyb F).kind)
      (fun p : F × F × F × F => cbc2Hybrid F p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : Hiding (((hybridEval F).tagged (AesHyb F).kind).lift PMF)
      (fun p : F × F × F × F => cbc2Hybrid F p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Hiding.of_lift _ _ (fun _ => [(.inr 0, []), (.inl (), []), (.inr 0, []), (.inl (), [])]) fun _ => rfl
  rw [hybridModel_eq]
  exact h

-- ...and transported to the plain circuit by the composition theorem.
theorem cbc2Plain_hiding :
    Hiding ((ABB F).model.tagged (ABB F).kind)
      (fun p : F × F × F × F => cbc2Plain F p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Hiding.transport (Realization.sum (aesByCircuit F) (Realization.id (ABB F))).realizes _
    (cbc2Hybrid_hiding F)

-- Delay, in the timed domain: in the hybrid, `enc` is one operation of latency 1
-- (so CBC of two blocks is 2); after instantiation, `enc` costs what the circuit
-- costs, two dependent multiplications (so 4).
local notation "𝕋" => Domain.timed F
def AesOp.timed (ℓ : Nat) : Model (AesOp 𝕋) F Sched where
  program o := match o with | .enc k m => Timed.after [k.time, m.time] ℓ (toyAes F k.val m.val)
  leak _ _ := []
def hybridTimed [Inhabited F] : Model (AesOp 𝕋 ⊞ Std 𝕋) F Sched := (AesOp.timed F 1).sum (Std.timed F)
example [Inhabited F] (k iv m₁ m₂ : F) :
    (Sched.output (hybridTimed F) (cbc2 (D := 𝕋) (σ := AesOp 𝕋 ⊞ Std 𝕋) ⟨k, 0⟩ ⟨iv, 0⟩ ⟨m₁, 0⟩ ⟨m₂, 0⟩)).2.time = 2 := rfl
def aesHandlerT : {β : Type} → AesOp 𝕋 β → Circ (Std 𝕋) β
  | _, .enc k m => toyAesCircuitD (D := 𝕋) k m
def plainHandlerT : {β : Type} → (AesOp 𝕋 ⊞ Std 𝕋) β → Circ (Std 𝕋) β := fun o => match o with
  | .inl o => aesHandlerT F o
  | .inr o => Circ.op o
example [Inhabited F] (k iv m₁ m₂ : F) :
    (Sched.output (Std.timed F)
      (Circ.handle (plainHandlerT F)
        (cbc2 (D := 𝕋) (σ := AesOp 𝕋 ⊞ Std 𝕋) ⟨k, 0⟩ ⟨iv, 0⟩ ⟨m₁, 0⟩ ⟨m₂, 0⟩))).2.time = 4 := rfl

/-! ### The UC shape: prove the hybrid protocol against *its own* specification first

The protocol is itself a functionality, `CBC`, with a program (the two
ciphertexts, defined through the AES *specification*) and a leak (none).
Its realisation over the AES-hybrid is proved once, with no knowledge of
how AES will be realised.  Later, any realisation of AES over the black box
composes with it, by `Realization.comp`, into a realisation of `CBC` over
the black box.  Nothing about the hybrid proof is revisited. -/

/-- The specification of the protocol, stated through the AES specification. -/
inductive CbcOp (D : Domain) : Sig where
  | run : D.S → D.S → D.S → D.S → CbcOp D (D.S × D.S)

def CbcId : Model (CbcOp 𝕀) F Id :=
  { program := fun o => match o with
      | .run k iv m₁ m₂ => pure (toyAes F k (iv + m₁), toyAes F k (toyAes F k (iv + m₁) + m₂)),
    leak := fun _ _ => [] }
noncomputable abbrev CBC : Functionality F := ⟨CbcOp 𝕀, Unit, fun _ => (), (CbcId F).lift PMF⟩

/-- The hybrid protocol as a handler for `CBC`. -/
def cbcHandler : {β : Type} → CbcOp 𝕀 β → Circ (AesHybrid F) β
  | _, .run k iv m₁ m₂ => cbc2Hybrid F k iv m₁ m₂

/-- **Done first, once, against the AES specification only.** -/
theorem cbc_realizes_hybrid :
    Realizes (AesHyb F).kind (CBC F).kind (cbcHandler F) (AesHyb F).model (CBC F).model := by
  refine ⟨fun _ _ => pure [(.inr 0, []), (.inl (), []), (.inr 0, []), (.inl (), [])], ?_⟩
  intro β o
  cases o
  simp [dist, cbcHandler, cbc2Hybrid, cbc2, add, Circ.op, Has.inj, Model.tagged, Functionality.sum, Model.sum,
    Std.kind, Std.ideal, AesId, CbcId, Lin.ideal, toyAes, run, Trace.seq]

noncomputable def cbcOverHybrid : Realization (CBC F) (AesHyb F) := ⟨cbcHandler F, cbc_realizes_hybrid F⟩

/-- **Done later, by composition**: plug in a realisation of AES over the
black box.  The result is a realisation of `CBC` over `Std` alone. -/
noncomputable def cbcOverABB : Realization (CBC F) (ABB F) :=
  (cbcOverHybrid F).comp (Realization.sum (aesByCircuit F) (Realization.id (ABB F)))

-- The composed implementation is literally the instantiated circuit.
example (k iv m₁ m₂ : F) : (cbcOverABB F).impl (CbcOp.run k iv m₁ m₂) = cbc2Plain F k iv m₁ m₂ := rfl

-- And a different AES realisation composes the same way, with the same hybrid proof.
noncomputable example (impl : F → F → Circ (Std 𝕀) F)
    (h : Realizes (ABB F).kind (AES F (toyAes F)).kind (aesHandler F impl) (ABB F).model (AES F (toyAes F)).model) :
    Realization (CBC F) (ABB F) :=
  (cbcOverHybrid F).comp (Realization.sum (aesCircuit F (toyAes F) impl h) (Realization.id (ABB F)))
end

end Glean
