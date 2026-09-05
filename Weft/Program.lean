import Lean
import Weft.Realization

/-!
# The `program` command: certificates with a checked implementation

A realisation's `impl` is a program for every domain, so it can do nothing
with a share except pass it to an operation.  Lean enforces that for a
computable `def`: comparing two shares needs a `DecidableEq (D.sh T)`
instance that does not exist, and a classical one makes the definition
noncomputable.  Not enforced by Lean: `noncomputable def`, `unsafe`,
`implemented_by`, `partial`, and a parameter of the certificate that
supplies a way to inspect shares (a callback over the domain, a
decidability dictionary).

`program` closes those gaps.  It declares the certificate and then checks
the fully applied `impl` term as it sits in it: every constant it uses,
transitively through this package's definitions, is computable, not
unsafe, and carries no `implemented_by` or `extern`; no parameter of the
certificate mentions a domain.  Simulators and proofs are unconstrained.

    program beaverMult (F : Type) [Field F] [Fintype F] [Inhabited F] : Realization (Mult F) (Pre F) :=
      { impl := ..., Sim := ..., real := ... }
-/
namespace Weft.Program
open Lean Elab Command Meta

/-- Constants that are the checked package: traverse into these, stop at the rest. -/
private def isLocalConst (n : Name) : Bool :=
  !([`Lean, `Init, `Std, `Mathlib, `Nat, `List, `Fin, `Prod, `Option, `Sum, `Sigma, `PUnit, `Unit, `Bool, `Eq,
    `Function, `id, `ite, `dite, `Decidable, `instDecidableEqNat, `Int] : List Name).any fun p => Name.isPrefixOf p n

/-- Why a constant is unacceptable in an implementation, if it is.  In
`strict` mode (the certificate's own term) noncomputable constants and
data axioms are rejected too; inside a computable definition Lean has
already checked that they sit in irrelevant positions. -/
private def offence (env : Environment) (strict : Bool) (n : Name) : Option String :=
  if n == ``sorryAx then some "sorry"
  else if strict && isNoncomputable env n then some "noncomputable"
  else match env.find? n with
    | some ci =>
      if ci.isUnsafe then some "unsafe"
      else if strict && n == ``Classical.choice then some "Classical.choice"
      else if !isLocalConst n then none   -- the standard library's externs are its own business
      else if (Compiler.getImplementedBy? env n).isSome then some "implemented_by"
      else if isExtern env n then some "extern"
      else if ci.isPartial then some "partial"
      else none
    | none => some "unknown"

/-- Check every constant of `e` outside its proofs, and transitively the
package's own definitions it uses. -/
private partial def checkExpr (env : Environment) (strict : Bool) (e : Expr) (visited : IO.Ref NameSet) : MetaM Unit := do
  let consts ← IO.mkRef ({} : NameSet)
  Meta.forEachExpr' e fun sub => do
    if (← Meta.isProof sub) then return false
    if let .const n _ := sub then consts.modify (·.insert n)
    return true
  for n in (← consts.get).toList do
    if (← visited.get).contains n then continue
    visited.modify (·.insert n)
    if let some why := offence env strict n then
      throwError "program: the implementation uses `{n}`, which is {why}"
    if isLocalConst n then
      if let some ci := env.find? n then
        if let some v := ci.value? then
          checkExpr env false v visited

/-- Peel the certificate's parameters, reject any that mentions a domain,
find `Realization.mk` and check its `impl`. -/
private def checkCertificate (declName : Name) : TermElabM Unit := do
  let env ← getEnv
  let some ci := env.find? declName | throwError "program: no declaration `{declName}`"
  let some v := ci.value? | throwError "program: `{declName}` has no value"
  forallTelescope ci.type fun params _ => do
    for p in params do
      let t ← inferType p
      if t.containsConst (· == ``Weft.Domain) then
        throwError "program: parameter `{← ppExpr p}` mentions a domain; its type is `{← ppExpr t}`.\n\
          A certificate's implementation must be generic in the domain and may not receive anything that inspects shares."
    let body := v.beta params
    let body ← whnfR body
    let some (fn, args) := (body.getAppFn.constName?.map (·, body.getAppArgs)) | throwError "program: cannot see the certificate's shape"
    unless fn == ``Weft.Realization.mk && args.size == 6 do
      throwError "program: expected `Realization.mk`, found `{fn}`"
    let impl := args[2]!
    let visited ← IO.mkRef ({} : NameSet)
    checkExpr env true impl visited

/-- `program name params : Realization F fs := body` declares `name` as a
(noncomputable, the simulator is a `PMF`) definition and checks its
implementation. -/
syntax (name := programCmd) (docComment)? "program " declId ppIndent(optDeclSig) declVal : command

@[command_elab programCmd] def elabProgram : CommandElab := fun stx => do
  let doc? := stx[0].getOptional?
  let declId : TSyntax ``Parser.Command.declId := ⟨stx[2]⟩
  let sig : TSyntax ``Parser.Command.optDeclSig := ⟨stx[3]⟩
  let val : TSyntax ``Parser.Command.declVal := ⟨stx[4]⟩
  let cmd ← match doc? with
    | some doc => `(command| $(⟨doc⟩):docComment noncomputable def $declId:declId $sig:optDeclSig $val:declVal)
    | none => `(command| noncomputable def $declId:declId $sig:optDeclSig $val:declVal)
  elabCommand cmd
  let name := (← getCurrNamespace) ++ declId.raw[0].getId
  liftTermElabM <| checkCertificate name
  logInfo m!"program: `{name}` certified; its implementation is a computable, domain-generic program."

end Weft.Program
