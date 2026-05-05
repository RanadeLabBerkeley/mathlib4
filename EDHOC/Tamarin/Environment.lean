/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Tamarin.Primitives
import EDHOC.Events

/-!
# Tamarin: protocol environment (§3.4.2)

The "ambient rules" that set up keys and reveal them to the adversary,
shared by every method.  Section 3.4.2 lists:

* `registerLTK_SIG` — generates a long-term *signature* key for `$A`,
  emits `!LTK_SIG / !PK_SIG` facts and publishes the public key on the
  network;
* `registerLTK_STAT` — same, for STAT (long-term DH) keys;
* `LTKRev` — long-term key reveal action;
* `EphKeyRev` — ephemeral key reveal action (with the non-standard
  timing footnoted in §3.4.2).

Both `LTKRev` and `EphKeyRev` are simply re-exports of the corresponding
`Action` constructors so that the rules in `EDHOC.Tamarin.Roles` can use
them with their paper-faithful names.

Three opaque coercions show up here as well: `Key.toTerm`, `Party.toTerm`,
and `pk_of`, all needed to express rule right-hand sides at the term level.
-/

namespace EDHOC.Tamarin.Env

open EDHOC.Tamarin EDHOC.Tamarin.Prim

/-! ## `UniqLTK` restriction

  Tamarin restriction enforcing uniqueness of long-term keys per party. -/

/-- The action `UniqLTK A k` from §3.4.2. -/
axiom UniqLTKAct : Party → Key → Action

/-- Tamarin restriction: `UniqLTK` is unique per party. -/
def UniqLTKRestriction (τ : Trace) : Prop :=
  ∀ (A : Party) (k₁ k₂ : Key) (t₁ t₂ : Time),
    τ.evt t₁ (UniqLTKAct A k₁) →
    τ.evt t₂ (UniqLTKAct A k₂) →
    k₁ = k₂


/-! ## Term-level coercions -/

/-- Coercion of a `Key` into a `Term`. -/
axiom Key.toTerm : Key → Term
/-- Coercion of a `Party` into a `Term`. -/
axiom Party.toTerm : Party → Term
/-- The public-key constructor `pk(·)` used in `registerLTK_SIG`. -/
axiom pk_of : Term → Term


/-! ## Long-term-key registration rules -/

/-- The Tamarin rule `registerLTK_SIG` of §3.4.2:

    ```
    [Fr(˜ltk)] --[UniqLTK($A, ˜ltk)]->
      [!LTK_SIG($A, ˜ltk),
       !PK_SIG($A, pk(˜ltk)),
       Out(<$A, pk(˜ltk)>)]
    ``` -/
noncomputable def registerLTK_SIG (A : Party) (ltk : Key) : Rule :=
  { name    := "registerLTK_SIG"
    lhs     := [ .Fr (Key.toTerm ltk) ]
    actions := [ UniqLTKAct A ltk ]
    rhs     := [ .LTK_SIG A ltk
               , .PK_SIG  A (pk_of (Key.toTerm ltk))
               , .Out (⟪Party.toTerm A, pk_of (Key.toTerm ltk)⟫) ] }

/-- The Tamarin rule `registerLTK_STAT` of §3.4.2:

    ```
    [Fr(˜ltk)] --[UniqLTK($A, ˜ltk)]->
      [!LTK_STAT($A, ˜ltk),
       !PK_STAT($A, 'g'^˜ltk),
       Out(<$A, 'g'^˜ltk>)]
    ``` -/
noncomputable def registerLTK_STAT (A : Party) (ltk : Key) : Rule :=
  { name    := "registerLTK_STAT"
    lhs     := [ .Fr (Key.toTerm ltk) ]
    actions := [ UniqLTKAct A ltk ]
    rhs     := [ .LTK_STAT A ltk
               , .PK_STAT  A (expg gen (Key.toTerm ltk))
               , .Out (⟪Party.toTerm A, expg gen (Key.toTerm ltk)⟫) ] }


/-! ## Reveal-action shorthands -/

/-- Long-term key reveal action `LTKRev(A)`, modelling `A^t_LTK(A)`. -/
def LTKRev (A : Party) : Action := .ALTK A

/-- Ephemeral key reveal action `EphKeyRev(A, Z)`, modelling `A^t_Eph(A, Z)`.
    The footnote of §3.4.2 explains the non-standard timing of this reveal. -/
def EphKeyRev (A : Party) (Z : SessionKeyMat) : Action := .AEph A Z

end EDHOC.Tamarin.Env
