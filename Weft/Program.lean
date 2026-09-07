import Lean
import Weft.Realization

/-!
# Checking implementations

`program` declares a realisation and checks its fully applied `impl` term.
It rejects domain-dependent certificate parameters and disallowed constants,
following references through the package's definitions.
The simulator and proof may remain noncomputable.

These checks supplement domain polymorphism:
Lean also permits noncomputable definitions, unsafe code and replacement implementations.
A certificate parameter could supply operations on shares.
The checker restricts these mechanisms in the implementation term.

    program beaverMult (F : Type) [Field F] [Fintype F] [Inhabited F] : Realization (Mult F) (Pre F) :=
      { impl := ..., Sim := ..., real := ... }
-/
namespace Weft.Program
open Lean Elab Command Meta

/-- Identify package constants for transitive checking. -/
private def isLocalConst (n : Name) : Bool :=
  !([`Lean, `Init, `Std, `Mathlib, `Nat, `List, `Fin, `Prod, `Option, `Sum, `Sigma, `PUnit, `Unit, `Bool, `Eq,
    `Function, `id, `ite, `dite, `Decidable, `instDecidableEqNat, `Int,
    `Array, `Vector, `Subarray, `ByteArray, `String, `Char, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec]
    : List Name).any fun p => Name.isPrefixOf p n

/-- Return the reason a constant is disallowed, if any.
Strict checking also rejects noncomputable constants and `Classical.choice`.
Inside a computable definition, Lean has already checked their computational relevance. -/
private def offence (env : Environment) (strict : Bool) (n : Name) : Option String :=
  if n == ``sorryAx then some "sorry"
  else if strict && isNoncomputable env n then some "noncomputable"
  else match env.find? n with
    | some ci =>
      if ci.isUnsafe then some "unsafe"
      else if strict && n == ``Classical.choice then some "Classical.choice"
      else if !isLocalConst n then none   -- Trust standard-library externs.
      else if (Compiler.getImplementedBy? env n).isSome then some "implemented_by"
      else if isExtern env n then some "extern"
      else if ci.isPartial then some "partial"
      else none
    | none => some "unknown"

/-- Check non-proof references in `e` and recursively inspect package definitions. -/
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

/-- Reject domain-dependent parameters,
then locate `Realization.mk` and check its implementation field. -/
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

/-- Declare a realisation and check its implementation.
The declaration is noncomputable to accommodate the `PMF` simulator. -/
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
