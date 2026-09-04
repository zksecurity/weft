# 004 — Generic over field types, no field names

## Choice
Shares are a type constructor: `D.S F` is a share of an `F`. Every
operation is generic over `F`; the field's algebra is a typeclass on `F`
(Mathlib's `Field`, plus an order where comparison is offered); a
capability entry `Cap.on f F` carries the field's instances; switching is
a capability over two field types. `⟦F⟧` is notation for `D.S F`.

## Alternatives
1. **One field per domain** (`Domain := ⟨F, S⟩`). The first design; the
   single-field special case, still used in the simpler files. Con:
   multi-field circuits impossible.
2. **Domains indexed by field names** (`Domains ι := ι → Domain`,
   features tagged `.on i f`). Pro: decidable equality on names. Con:
   "field 1, field 2" is not how anyone thinks; the name is an
   indirection to the type that carries the algebra anyway.

## Why types
A field is its type with its instances. Operations infer the field from
their argument, a mismatch is a type error, `rand F` names the field it
draws from, and the ideal model is assembled from the instances the
capability entry carries. Cost: requests mention a `Type`, so `Sig` is
universe-polymorphic.
