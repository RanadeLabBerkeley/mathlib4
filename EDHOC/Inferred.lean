/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Properties

/-!
# Inferred properties on the initiator side (§3.2.4)

> "Because both our above notions of agreement ensure agreement on
> identities, roles and session key material, all methods passing
> verification of those are also resistant to KCI attacks."

> "from the injective agreement properties it follows that each party is
> assured the identity of its peer upon completion."

The paper's §3.2.4 states three corollaries of injective / implicit
agreement, but only spells them out on the *initiator-completing* side:

* **KCI** (Key-Compromise Impersonation) **resistance** — even if the
  long-term key of the believed peer leaks, the initiator's run remains
  bound to a matching responder run;
* **UKS** (Unknown Key-Share) **resistance** — the believed responder is
  the unique party agreeing on `Z` with the initiator;
* **Entity authentication** — the initiator is assured of the responder's
  identity once it completes.

This file gives the predicates and proves the entity-authentication
corollary; the responder-side mirrors live in `EDHOC.Dual`.
-/

namespace EDHOC

/-! ## Definitions -/

/-- KCI (Key-Compromise Impersonation) resistance, initiator side: any
    completed initiator run with a believed responder must be paired with
    a started responder run by that very party — unless `R`'s long-term
    key has leaked. -/
def KCIResistant (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
    IC τ t I R Z S →
        (∃ t' S', t' ⋖ t ∧ RS_self τ t' R Z S')
      ∨ (∃ t', t' ⋖ t ∧ ALTK τ t' R)

/-- UKS (Unknown Key-Share) resistance, initiator side: the believed
    responder is the unique party agreeing on `Z` with `I`. -/
def UKSResistant (τ : Trace) : Prop :=
  ∀ (I R R' : Party) (Z : SessionKeyMat) (S S' : ParamSet) (t t' : Time),
    IC τ t  I R  Z S  →
    RC τ t' I R' Z S' →
    R = R'

/-- Entity authentication of the peer, initiator side: any completed
    initiator run is preceded by a matching started responder run. -/
def EntityAuth (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
    IC τ t I R Z S → ∃ t' S', t' ⋖ t ∧ RS_self τ t' R Z S'


/-! ## Initiator-side proofs

  Entity authentication follows immediately from `InjAgreeI` once the
  long-term-key escape clause is closed off; KCI and UKS are obtained
  from `Table1` in `EDHOC.Table1`. -/

/-- §3.2.4 (last paragraph): "from the injective agreement properties it
    follows that each party is assured the identity of its peer upon
    completion." -/
theorem entityAuth_of_injAgreeI
    (τ : Trace) (h : InjAgreeI τ)
    (hLTK : ∀ t R, ¬ ALTK τ t R) :
    EntityAuth τ := by
  intro I R Z S t hIC
  rcases h I R Z S t hIC with ⟨⟨t₁, hRS, hbef⟩, _⟩ | ⟨t₁, hAltk, _⟩
  · exact ⟨t₁, S, hbef, hRS⟩
  · exact (hLTK _ _ hAltk).elim

end EDHOC
