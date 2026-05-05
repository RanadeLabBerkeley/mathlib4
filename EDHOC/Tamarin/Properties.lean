/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Tamarin.Environment
import EDHOC.Properties

/-!
# Tamarin: property encoding (§3.5)

The paper checks the high-level properties of `EDHOC.Properties` by
encoding them as Tamarin all-traces lemmas.  As a sanity check we
transcribe the `secrecyPFS` lemma and prove both directions of the
correspondence with our high-level `PFS`.

The lemma in `.spthy` syntax (paper, page 14):

```
lemma secrecyPFS:
  all-traces
  "All u v sk #t3 #t2.
    (K(sk)@t3 & CompletedRun(u, v, sk)@t2) ==>
      ( (Ex #t1. LTKRev(u)@t1 & #t1 < #t2)
      | (Ex #t1. LTKRev(v)@t1 & #t1 < #t2)
      | (Ex #t1. EphKeyRev(sk)@t1))"
```
-/

namespace EDHOC.Tamarin.Encoding

open EDHOC.Tamarin.Env

/-- Tamarin's `EphKeyRev(sk)` does not name the party.  §3.5 explains:
    "models that the ephemeral key is revealed for either `I` or `R`, or
    both".  We translate this as "there exists a party `u` such that
    `A^{t}_Eph(u, sk)` holds". -/
def EphKeyRev (τ : Trace) (t : Time) (Z : SessionKeyMat) : Prop :=
  ∃ u, AEph τ t u Z

/-- The Tamarin lemma `secrecyPFS` rendered as a Lean `Prop`. -/
def secrecyPFS (τ : Trace) : Prop :=
  ∀ (u v : Party) (Z : SessionKeyMat) (t₂ t₃ : Time),
    K τ t₃ (sk_term Z) →
    CompletedRun τ t₂ u v Z →
        (∃ t₁, ALTK τ t₁ u ∧ t₁ ⋖ t₂)
      ∨ (∃ t₁, ALTK τ t₁ v ∧ t₁ ⋖ t₂)
      ∨ (∃ t₁, EphKeyRev τ t₁ Z)

/-- The high-level `PFS` of §3.2.1 implies the Tamarin-style `secrecyPFS`. -/
theorem PFS_implies_secrecyPFS
    (τ : Trace) (h : PFS τ) : secrecyPFS τ := by
  intro u v Z t₂ t₃ hK hCR
  rcases h u v Z t₂ t₃ hK hCR with
      h₁ | h₂ | ⟨t₁, hAEph⟩ | ⟨t₁, hAEph⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)
  · exact Or.inr (Or.inr ⟨t₁, ⟨_, hAEph⟩⟩)
  · exact Or.inr (Or.inr ⟨t₁, ⟨_, hAEph⟩⟩)

/-- Conversely, `secrecyPFS` plus the disambiguation of *which* party had
    its ephemeral key revealed implies `PFS`.  The disambiguation is needed
    because `EphKeyRev` is existential over the party. -/
theorem secrecyPFS_implies_PFS
    (τ : Trace) (h : secrecyPFS τ)
    (party_of_eph :
      ∀ I R t Z u, AEph τ t u Z → AEph τ t I Z ∨ AEph τ t R Z) :
    PFS τ := by
  intro I R Z t₂ t₃ hK hCR
  rcases h I R Z t₂ t₃ hK hCR with
      h₁ | h₂ | ⟨t₁, ⟨u, hAEph⟩⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)
  · rcases party_of_eph I R _ _ _ hAEph with hI | hR
    · exact Or.inr (Or.inr (Or.inr ⟨t₁, hI⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨t₁, hR⟩))

end EDHOC.Tamarin.Encoding
