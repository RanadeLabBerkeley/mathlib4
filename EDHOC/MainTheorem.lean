/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Dual
import EDHOC.Secrecy

/-!
# The headline EDHOC security theorem

The single statement summarising the paper's main result.  Every honest
run of every EDHOC method enjoys

* the **five Tamarin-verified properties** of Table 1
  (`PFS`, `InjAgreeI/R`, `ImpAgreeI/R`),
* **KCI resistance** on both sides (its escape clause is built in),

*unconditionally*; and the §3.2.4 inferred properties

* **mutual entity authentication**,
* **UKS resistance** on both sides plus the combined `UKSFull`,
* **honest-world secrecy** of the session key material,

*conditional on the honesty hypotheses* the paper requires.

The bundle is split into two structures so that the unconditional
consequences can be quoted in isolation when no honesty hypothesis is
available.

A "slogan" corollary `EDHOC_safe_world` instantiates the strongest
honesty hypothesis (no leaks at all), making every escape clause
collapse and yielding the cleanest user-facing statement.
-/

namespace EDHOC

/-! ## Bundles -/

/-- The unconditional bundle: properties that hold on every honest run
    *without* any further assumption on the adversary's reveals.  Each
    constituent has its own escape-clause built in. -/
structure EDHOC_main_unconditional (τ : Trace) : Prop where
  /-- Perfect forward secrecy of the session key material. -/
  pfs        : PFS τ
  /-- Injective agreement, initiator side. -/
  injAgreeI  : InjAgreeI τ
  /-- Injective agreement, responder side. -/
  injAgreeR  : InjAgreeR τ
  /-- Implicit agreement, initiator side. -/
  impAgreeI  : ImpAgreeI τ
  /-- Implicit agreement, responder side. -/
  impAgreeR  : ImpAgreeR τ
  /-- KCI resistance, initiator side. -/
  kciI       : KCIResistant τ
  /-- KCI resistance, responder side. -/
  kciR       : KCIResistantR τ

/-- The full Main-Theorem bundle.  Combines the unconditional consequences
    with the conditional ones, each guarded by exactly the honesty
    hypothesis the paper requires. -/
structure EDHOC_main_security (τ : Trace) : Prop where
  /-- The seven unconditional properties. -/
  unconditional : EDHOC_main_unconditional τ
  /-- Mutual entity authentication, given no long-term key ever leaks. -/
  entity_auth_of_no_ltk_leak :
      (∀ t A, ¬ ALTK τ t A) → EntityAuth τ ∧ EntityAuthR τ
  /-- UKS resistance from the initiator side, given the runs in question
      are honest (no LTK / Eph leaks for the participants). -/
  uks_I_of_honest :
      (∀ I R Z S t, IC τ t I R Z S →
          (∀ t₀, ¬ ALTK τ t₀ R)
        ∧ (∀ t₀, ¬ AEph τ t₀ R Z)
        ∧ (∀ t₀, ¬ AEph τ t₀ I Z))
      → UKSResistant τ
  /-- UKS resistance from the responder side under the symmetric honesty
      hypothesis. -/
  uks_R_of_honest :
      (∀ I R Z S t, RC τ t I R Z S →
          (∀ t₀, ¬ ALTK τ t₀ I)
        ∧ (∀ t₀, ¬ AEph τ t₀ R Z)
        ∧ (∀ t₀, ¬ AEph τ t₀ I Z))
      → UKSResistantR τ
  /-- The combined "session key material pins down both peers" statement,
      under the initiator-side honesty hypothesis. -/
  uks_full_of_honest :
      (∀ I R Z S t, IC τ t I R Z S →
          (∀ t₀, ¬ ALTK τ t₀ R)
        ∧ (∀ t₀, ¬ AEph τ t₀ R Z)
        ∧ (∀ t₀, ¬ AEph τ t₀ I Z))
      → UKSFull τ
  /-- Honest-world secrecy of the session key material: no global key
      reveals ⇒ adversary cannot know any completed run's `Z`. -/
  honest_world_secrecy_of_no_leaks :
      (∀ t A, ¬ ALTK τ t A) → (∀ t A Z, ¬ AEph τ t A Z) →
      ∀ {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time},
        CompletedRun τ t₂ I R Z → ¬ K τ t₃ (sk_term Z)


/-! ## The Main Theorem -/

/-- **Main Theorem.**  Every honest run of every EDHOC method enjoys the
    bundle `EDHOC_main_security`: all five Tamarin-verified properties, KCI
    resistance on both sides unconditionally, and the inferred properties
    (entity auth, UKS, honest-world secrecy) under their respective
    honesty hypotheses. -/
theorem EDHOC_main
    (m : Method) (τ : Trace) (h : honestRun m τ) :
    EDHOC_main_security τ := by
  have V := Table1 m τ h
  refine
    { unconditional :=
        { pfs       := V.pfs
          injAgreeI := V.injAgreeI
          injAgreeR := V.injAgreeR
          impAgreeI := V.impAgreeI
          impAgreeR := V.impAgreeR
          kciI      := KCI_of_Table1 m τ h
          kciR      := KCI_R_of_Table1 m τ h }
      entity_auth_of_no_ltk_leak := fun noLTK =>
        ⟨ entityAuth_of_injAgreeI τ V.injAgreeI noLTK
        , entityAuth_R_of_injAgreeR τ V.injAgreeR noLTK ⟩
      uks_I_of_honest := UKS_of_Table1 m τ h
      uks_R_of_honest := UKS_R_of_Table1 m τ h
      uks_full_of_honest := UKSFull_of_Table1 m τ h
      honest_world_secrecy_of_no_leaks := fun noLTK noEph =>
        honest_world_secrecy τ V.pfs noLTK noEph }


/-! ## Slogan corollary -/

/-- **EDHOC is secure (slogan form).**  Specialise `EDHOC_main` to the
    strongest honesty hypothesis: no long-term or ephemeral keys ever
    revealed.  All escape clauses collapse, leaving the clean statement
    of every verified and inferred property. -/
theorem EDHOC_safe_world
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (noLTK : ∀ t A, ¬ ALTK τ t A)
    (noEph : ∀ t A Z, ¬ AEph τ t A Z) :
    EDHOC_main_unconditional τ
    ∧ EntityAuth τ ∧ EntityAuthR τ
    ∧ UKSResistant τ ∧ UKSResistantR τ ∧ UKSFull τ
    ∧ ∀ {I R : Party} {Z : SessionKeyMat} {t₂ t₃ : Time},
        CompletedRun τ t₂ I R Z → ¬ K τ t₃ (sk_term Z) := by
  have sec := EDHOC_main m τ h
  obtain ⟨eaI, eaR⟩ := sec.entity_auth_of_no_ltk_leak noLTK
  -- Both honesty hypotheses follow uniformly from the global no-leak
  -- assumptions.
  have hH_IC :
      ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
        IC τ t I R Z S →
        (∀ t₀, ¬ ALTK τ t₀ R)
      ∧ (∀ t₀, ¬ AEph τ t₀ R Z)
      ∧ (∀ t₀, ¬ AEph τ t₀ I Z) := fun _ _ _ _ _ _ =>
    ⟨fun _ => noLTK _ _, fun _ => noEph _ _ _, fun _ => noEph _ _ _⟩
  have hH_RC :
      ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
        RC τ t I R Z S →
        (∀ t₀, ¬ ALTK τ t₀ I)
      ∧ (∀ t₀, ¬ AEph τ t₀ R Z)
      ∧ (∀ t₀, ¬ AEph τ t₀ I Z) := fun _ _ _ _ _ _ =>
    ⟨fun _ => noLTK _ _, fun _ => noEph _ _ _, fun _ => noEph _ _ _⟩
  exact ⟨ sec.unconditional
        , eaI, eaR
        , sec.uks_I_of_honest hH_IC
        , sec.uks_R_of_honest hH_RC
        , sec.uks_full_of_honest hH_IC
        , sec.honest_world_secrecy_of_no_leaks noLTK noEph ⟩

end EDHOC
