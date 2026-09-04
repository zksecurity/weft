import Compose

/-!
# One notion: functionalities and their realisations

There is no distinction in kind between "the MPC's multiplication" and
"an AES circuit".  Both are **functionalities**: an interface (a signature)
with a `program` and a `leak`, and a public *kind* for each request (the
adversary knows the program).  What differs is how they come to exist:

* *primitive* functionalities are provided by the MPC; their realisation
  is the trusted identity, and their price is on the MPC's price list;
* *derived* functionalities are realised by a circuit over other
  functionalities, with a `Realizes` proof; their price is derived.

Realisations compose (that is the composition theorem), so
functionalities and realisations form a category: objects are
interfaces, morphisms are "implemented over", identities are trust, and
composition is inlining.  A circuit is a morphism out of a one-operation
functionality; a gadget is such a morphism with assumptions;
`Has τ σ` is the trivial morphism `τ → τ ⊞ σ`.
-/
namespace Glean

/-- A functionality: what it offers, what is public about a request, what
it computes, what it leaks. -/
structure Functionality (L : Type) where
  ops   : Sig
  K     : Type
  kind  : {β : Type} → ops β → K
  model : Model ops L PMF          -- program + leak, for every operation

/-- `F` is realised over `G`: every operation of `F` is a circuit over `G`
whose run is distributed as `F`'s program with the view simulated from
`F`'s declared record. -/
structure Realization {L : Type} (F G : Functionality L) where
  impl     : {β : Type} → F.ops β → Circ G.ops β
  realizes : Realizes G.kind F.kind impl G.model F.model

namespace Realization
variable {L : Type}

/-- The trusted realisation: a functionality the MPC provides natively. -/
def id (F : Functionality L) : Realization F F where
  impl o := Circ.op o
  realizes := Realizes.id F.kind F.model

/-- Composition is inlining, and `Realizes` composes by the composition theorem. -/
def comp {F G H : Functionality L} (f : Realization F G) (g : Realization G H) : Realization F H where
  impl o := Circ.handle g.impl (f.impl o)
  realizes := Realizes.comp f.realizes g.realizes
end Realization

/-- The sum of two functionalities: both interfaces, kinds tagged by side. -/
def Functionality.sum {L : Type} (F G : Functionality L) : Functionality L where
  ops := F.ops ⊞ G.ops
  K := F.K ⊕ G.K
  kind o := match o with | .inl o => .inl (F.kind o) | .inr o => .inr (G.kind o)
  model := F.model.sum G.model

namespace Realization
variable {L : Type}

/-- Feature inclusion is a realisation. -/
def inl (F G : Functionality L) : Realization F (F.sum G) where
  impl o := Circ.call (Sig.Sum.inl o) .pure
  realizes := by
    refine ⟨fun k l => pure [(Sum.inl k, l)], ?_⟩
    intro β o
    simp only [dist, Model.tagged, Functionality.sum, Model.sum, run, Trace.seq, Trace.zero, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.map_bind, PMF.pure_map, PMF.pure_bind]
    rfl

/-- Realise a sum by realising each summand. -/
def sum {F F' G : Functionality L} (f : Realization F G) (f' : Realization F' G) :
    Realization (F.sum F') G where
  impl o := match o with | .inl o => f.impl o | .inr o => f'.impl o
  realizes := by
    obtain ⟨S, hS⟩ := f.realizes
    obtain ⟨S', hS'⟩ := f'.realizes
    refine ⟨fun k l => match k with | .inl k => S k l | .inr k => S' k l, ?_⟩
    intro β o
    rcases o with o | o
    · exact hS o
    · exact hS' o
end Realization

/-- A circuit with a spec and a declared leak *is* a functionality with one
operation.  (A gadget is this plus assumptions; assumptions are the domain
on which the program is defined.) -/
noncomputable def Functionality.ofCircuit {L I O : Type} (spec : I → PMF O) (declared : I → O → List L) :
    Functionality L :=
  ⟨Gadget.OpOf I O, Unit, fun _ => (),
   { program := fun o => match o with | .call i => spec i,
     leak := fun o x => match o with | .call i => declared i x }⟩

/-- The handler of a one-operation functionality. -/
def circHandler {σ : Sig} {I O : Type} (c : I → Circ σ O) : {β : Type} → Gadget.OpOf I O β → Circ σ β
  | _, .call i => c i

/-- A gadget whose assumptions always hold, as a realisation of its own model. -/
noncomputable def Realization.ofGadget {L I O : Type} {G : Functionality L} (g : Gadget G.model I O)
    (h : g.RealizesModel G.kind) (hA : ∀ i, g.Assumptions i) :
    Realization ⟨Gadget.OpOf I O, Unit, fun _ => (), g.toModel⟩ G :=
  ⟨g.impl, g.realizes G.kind h hA⟩

/-! ## Example: a protocol over an AES functionality, instantiated two ways -/

section AES
variable (F : Type) [Field F]
local notation "𝕀" => Domain.ideal F

-- The AES block function, whatever it is: the *spec* of the functionality
-- (key, block ↦ ciphertext; stand-in types).
variable (aes : F → F → F)

/-- The AES functionality: one operation, computes `aes`, leaks nothing. -/
inductive AesOp (D : Domain) : Sig where
  | enc : D.S → D.S → AesOp D D.S

/-- Its (deterministic) model, for evaluation... -/
def AesId : Model (AesOp 𝕀) F Id :=
  { program := fun o => match o with | .enc k m => pure (aes k m), leak := fun _ _ => [] }
/-- ...and the functionality. -/
noncomputable abbrev AES : Functionality F := ⟨AesOp 𝕀, Unit, fun _ => (), (AesId F aes).lift PMF⟩

/-- The arithmetic black box, as a functionality. -/
noncomputable abbrev ABB : Functionality F := ⟨Std 𝕀, Fin 3, Std.kind, (Std.ideal F).lift PMF⟩

/-- A protocol written against AES *and* the ABB: encrypt two blocks in
CBC mode.  It knows nothing about how AES is realised. -/
def cbc2 {D : Domain} {σ : Sig} [Has (AesOp D) σ] [Has (Lin D) σ] (k iv m₁ m₂ : D.S) : Circ σ (D.S × D.S) := do
  let x₁ ← add iv m₁
  let c₁ ← Circ.op (AesOp.enc k x₁)
  let x₂ ← add c₁ m₂
  let c₂ ← Circ.op (AesOp.enc k x₂)
  pure (c₁, c₂)

/-- Instantiation 1: the MPC offers AES natively (trusted, priced on its list). -/
noncomputable def aesNative : Realization (AES F aes) (AES F aes) := Realization.id _

/-- Instantiation 2: AES realised by a circuit over the ABB (S-boxes by
inversion, linear layers free).  Its `Realizes` proof is the only new
obligation, and it is about this circuit alone. -/
def aesHandler (impl : F → F → Circ (Std 𝕀) F) : {β : Type} → AesOp 𝕀 β → Circ (Std 𝕀) β
  | _, .enc k m => impl k m

noncomputable def aesCircuit (impl : F → F → Circ (Std 𝕀) F)
    (h : Realizes (ABB F).kind (AES F aes).kind (aesHandler F impl) (ABB F).model (AES F aes).model) :
    Realization (AES F aes) (ABB F) :=
  ⟨aesHandler F impl, h⟩

/-- Either way, `cbc2`'s privacy is proved once, against `AES ⊞ ABB`, and
transported to whichever realisation is plugged in. -/
example (impl) (h) (I : Type) (P : I → Circ ((AES F aes).sum (ABB F)).ops (F × F))
    (hP : Hiding (((AES F aes).sum (ABB F)).model.tagged ((AES F aes).sum (ABB F)).kind) P) :
    Hiding ((ABB F).model.tagged (ABB F).kind) (fun i => Circ.handle
      (Realization.sum (aesCircuit F aes impl h) (Realization.id (ABB F))).impl (P i)) :=
  Hiding.transport (Realization.sum (aesCircuit F aes impl h) (Realization.id (ABB F))).realizes P hP
end AES

/-! ## A complete instance: a specification, a circuit, and the proof that it implements it -/

section Complete
variable (F : Type) [Field F]
local notation "𝕀" => Domain.ideal F

/-- The specification: a functionality `SqRev` that returns `x²` and
publishes it.  Program and leak are the whole specification. -/
inductive SqOp (D : Domain) : Sig where
  | sq : D.S → SqOp D D.F

def SqRevId : Model (SqOp 𝕀) F Id :=
  { program := fun o => match o with | .sq x => pure (x * x),
    leak := fun o v => match o with | .sq _ => [v] }
noncomputable abbrev SqRev : Functionality F := ⟨SqOp 𝕀, Unit, fun _ => (), (SqRevId F).lift PMF⟩

/-- A circuit with that specification: one multiplication, then reveal. -/
def sqRevCircuit : {β : Type} → SqOp 𝕀 β → Circ (Std 𝕀) β
  | _, .sq x => do
    let p ← mul x x
    reveal p

/-- ...and the proof that it implements it: the program agrees on the nose,
and the view is a multiplication record and a reveal of exactly what the
specification declares, so the simulator replays the declared leak. -/
theorem sqRevCircuit_realizes :
    Realizes (ABB F).kind (SqRev F).kind (sqRevCircuit F) (ABB F).model (SqRev F).model := by
  refine ⟨fun _ l => pure [(1, []), (2, l)], ?_⟩
  intro β o
  cases o
  simp [dist, sqRevCircuit, mul, reveal, Circ.op, Has.inj, Model.tagged, Model.sum, Std.kind, Std.ideal,
    SqRevId, Lin.ideal, Mult.ideal, Reveal.ideal, run, Trace.seq]

/-- The circuit, packaged as a realisation of the specification. -/
noncomputable def sqRev : Realization (SqRev F) (ABB F) := ⟨sqRevCircuit F, sqRevCircuit_realizes F⟩

/-- A caller composes by the specification alone: it sees `SqOp` with
program `x²` and leak `[x²]`, never the circuit. -/
def useSq {σ : Sig} [Has (SqOp 𝕀) σ] [Has (Lin 𝕀) σ] (a b : F) : Circ σ F := do
  let s ← add (D := 𝕀) a b
  Circ.op (SqOp.sq (D := 𝕀) s)

-- What the caller may assume, by evaluation against the specification:
example (a b : F) :
    leak ((SqRevId F).sum (Std.ideal F)) (useSq F (σ := (SqRev F).ops ⊞ (ABB F).ops) a b)
      = [(a + b) * (a + b)] := rfl
-- ...and what it gets after inlining the circuit (same reveals here, by construction):
example (a b : F) :
    leak (Std.ideal F) (Circ.handle (Realization.sum (sqRev F) (Realization.id (ABB F))).impl
      (useSq F (σ := (SqRev F).ops ⊞ (ABB F).ops) a b)) = [(a + b) * (a + b)] := rfl
end Complete

end Glean
