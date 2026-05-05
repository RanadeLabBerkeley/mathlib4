/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Preliminaries

The minimal vocabulary that the rest of the EDHOC formalisation builds on:

* tiny, Mathlib-free predicates `Injective` and `Injective₂`,
* the abstract term algebra: `Party`, `Term`, `Key`, `Eph` and the pair
  constructor `⟪·, ·⟫`,
* timestamps: `Time`, the strict-before relation `⋖`, equality `=ₜ`.

Everything is opaque (`axiom`-introduced) so that this file is independent
of any concrete cryptographic library.  Only properties used elsewhere are
postulated.

This file corresponds to the parts of §3.1 and §3.2 of arXiv:2007.11427v3
that establish the vocabulary, before any security predicate is defined.
-/

namespace EDHOC

/-! ## Basic predicates

  Local re-declarations to keep the EDHOC library Mathlib-free. -/

/-- A function is injective. -/
def Injective {α β : Sort _} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- A binary function is injective in both arguments jointly. -/
def Injective₂ {α β γ : Sort _} (f : α → β → γ) : Prop :=
  ∀ a₁ a₂ b₁ b₂, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂


/-! ## Term algebra and parties

  The Dolev–Yao view of messages as terms in an algebra of function symbols.
  Section 3 is parametric in the underlying signature; we postulate the four
  sorts the paper actually uses.

  * `Party` — protocol identities (`$A` in the Tamarin code),
  * `Term`  — messages exchanged on the wire,
  * `Key`   — long-term key material (signature secret keys for SIG, static
              DH secrets for STAT),
  * `Eph`   — ephemeral private keys.

  The constructor `Term.pair` reflects the tuples `⟨·, ·⟩` of §3.2. -/

/-- Protocol identities. -/
axiom Party : Type
/-- Messages of the term algebra. -/
axiom Term  : Type
/-- Long-term private keys. -/
axiom Key   : Type
/-- Ephemeral private keys. -/
axiom Eph   : Type

/-- A canonical inhabitant of `Party`. -/
axiom Party.default : Party
/-- A canonical inhabitant of `Term`. -/
axiom Term.default  : Term
/-- A canonical inhabitant of `Key`. -/
axiom Key.default   : Key
/-- A canonical inhabitant of `Eph`. -/
axiom Eph.default   : Eph

noncomputable instance : Inhabited Party := ⟨Party.default⟩
noncomputable instance : Inhabited Term  := ⟨Term.default⟩
noncomputable instance : Inhabited Key   := ⟨Key.default⟩
noncomputable instance : Inhabited Eph   := ⟨Eph.default⟩

/-- The pair `⟨t₁, t₂⟩` in the term algebra (§3.2). -/
axiom Term.pair : Term → Term → Term
@[inherit_doc Term.pair]
notation "⟪" a ", " b "⟫" => Term.pair a b

/-- Tuples extract componentwise — the example formula in §3.2 reads
    `K^t(⟨k, k'⟩) → K^t(k) ∧ K^t(k')`, which relies on this injectivity. -/
axiom Term.pair_inj : Injective₂ Term.pair


/-! ## Timestamps

  Section 3.2 introduces timestamps as elements of a quasi-order `⋖`, with
  `t₁ ⋖ t₂` meaning "`t₁` is before `t₂`".  Two events of the same type
  cannot share a timestamp — this constraint is axiomatised in
  `EDHOC.Trace`. -/

/-- The opaque type of timestamps. -/
axiom Time : Type
/-- A canonical inhabitant of `Time`. -/
axiom Time.default : Time
noncomputable instance : Inhabited Time := ⟨Time.default⟩

/-- Strict-before relation on timestamps (the `⋖` of the paper). -/
axiom before : Time → Time → Prop
@[inherit_doc before]
infix:50 " ⋖ " => before

/-- Equality of timestamps (the `.=` of the paper). -/
def teq (t₁ t₂ : Time) : Prop := t₁ = t₂
@[inherit_doc teq]
infix:50 " =ₜ " => teq

/-- The strict-before relation is irreflexive. -/
axiom before_irrefl : ∀ t, ¬ (t ⋖ t)
/-- The strict-before relation is transitive. -/
axiom before_trans : ∀ a b c, a ⋖ b → b ⋖ c → a ⋖ c

end EDHOC
