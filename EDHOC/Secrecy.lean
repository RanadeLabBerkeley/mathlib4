/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Table1

/-!
# Honest-world secrecy

Not stated in the paper, but the natural user-facing reading of `PFS`.
The paper writes PFS in *contrapositive* form: "if the adversary knows
`Z`, then *some* key must have leaked."  Reading it forward gives the
slogan-friendly statement:

> If no party's long-term or ephemeral keys are ever revealed, then the
> adversary never learns the session key.

We provide:

* `honest_world_secrecy` — derived from any `PFS τ` directly;
* `honest_world_secrecy_of_Table1` — specialisation to honest runs of
  any EDHOC method via `Table1`;
* `honest_world_secrecy_local`(`_of_Table1`) — strengthened versions
  whose no-leak hypothesis is restricted to *the parties of the
  particular run* rather than all parties globally.
-/

namespace EDHOC

/-! ## Global no-leak versions -/

/-- **Honest-world secrecy (general).**  Under any trace satisfying `PFS`,
    if no long-term or ephemeral keys are ever revealed, then the adversary
    cannot know the session key material `Z` of a completed run, at any
    time.  Direct contrapositive of `PFS`. -/
theorem honest_world_secrecy
    (τ : Trace) (h : PFS τ)
    (noLTK : ∀ t A, ¬ ALTK τ t A)
    (noEph : ∀ t A Z, ¬ AEph τ t A Z)
    {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time}
    (hCR : CompletedRun τ t₂ I R Z) :
    ¬ K τ t₃ (sk_term Z) := by
  intro hK
  rcases h I R Z t₂ t₃ hK hCR with
      ⟨t₁, hLTK, _⟩ | ⟨t₁, hLTK, _⟩ | ⟨t₁, hEph⟩ | ⟨t₁, hEph⟩
  · exact noLTK t₁ I hLTK
  · exact noLTK t₁ R hLTK
  · exact noEph t₁ R Z hEph
  · exact noEph t₁ I Z hEph

/-- **Honest-world secrecy for EDHOC.**  Specialisation to any of the four
    EDHOC methods of Table 1.

    > "On any honest run of any EDHOC method, in a world where no keys are
    >  ever revealed, the session key material remains secret from the
    >  adversary forever." -/
theorem honest_world_secrecy_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (noLTK : ∀ t A, ¬ ALTK τ t A)
    (noEph : ∀ t A Z, ¬ AEph τ t A Z)
    {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time}
    (hCR : CompletedRun τ t₂ I R Z) :
    ¬ K τ t₃ (sk_term Z) :=
  honest_world_secrecy τ (Table1 m τ h).pfs noLTK noEph hCR


/-! ## Localised (per-run) no-leak versions

  `honest_world_secrecy` quantifies the no-leak hypotheses *globally*
  (no LTK ever leaks for any party, no Eph ever leaks for any party / Z).
  The paper's actual reading of PFS only requires that the *two parties
  of the run in question* keep their LTK / Eph private — strictly weaker,
  and more realistic. -/

/-- Honest-world secrecy under hypotheses local to the parties of the
    completed run only.  `honest_world_secrecy` is the obvious specialisation. -/
theorem honest_world_secrecy_local
    (τ : Trace) (h : PFS τ)
    {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time}
    (hCR : CompletedRun τ t₂ I R Z)
    (noLTK_I : ∀ t, ¬ ALTK τ t I)
    (noLTK_R : ∀ t, ¬ ALTK τ t R)
    (noEph_I : ∀ t, ¬ AEph τ t I Z)
    (noEph_R : ∀ t, ¬ AEph τ t R Z) :
    ¬ K τ t₃ (sk_term Z) := by
  intro hK
  rcases h I R Z t₂ t₃ hK hCR with
      ⟨t₁, hLTK, _⟩ | ⟨t₁, hLTK, _⟩ | ⟨t₁, hEph⟩ | ⟨t₁, hEph⟩
  · exact noLTK_I t₁ hLTK
  · exact noLTK_R t₁ hLTK
  · exact noEph_R t₁ hEph
  · exact noEph_I t₁ hEph

/-- Localised honest-world secrecy specialised to honest runs of any EDHOC
    method via `Table1`. -/
theorem honest_world_secrecy_local_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ)
    {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time}
    (hCR : CompletedRun τ t₂ I R Z)
    (noLTK_I : ∀ t, ¬ ALTK τ t I)
    (noLTK_R : ∀ t, ¬ ALTK τ t R)
    (noEph_I : ∀ t, ¬ AEph τ t I Z)
    (noEph_R : ∀ t, ¬ AEph τ t R Z) :
    ¬ K τ t₃ (sk_term Z) :=
  honest_world_secrecy_local τ (Table1 m τ h).pfs hCR noLTK_I noLTK_R noEph_I noEph_R

end EDHOC
