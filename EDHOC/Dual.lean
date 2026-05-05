/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Table1

/-!
# Inferred properties on the responder side

`EDHOC.Inferred` defines the §3.2.4 inferred properties only on the
initiator-completing side, mirroring the paper.  The paper notes "the
corresponding property for `R` is analogous"; here we make those formal.

Each definition is a literal mirror of its initiator-side analogue, with
the roles of `IS / IS_self` and `RS / RS_self` swapped, and the long-term-
key escape clause re-targeted at the believed initiator `I`.

We also introduce a slightly stronger combined notion `UKSFull`: both
peer identities are pinned down by `Z`, derived from `Table1.impAgreeI`'s
uniqueness conjunct.
-/

namespace EDHOC

/-! ## R-side dual predicates -/

/-- Entity authentication on the responder side: any completed responder
    run is preceded by some matching started initiator run. -/
def EntityAuthR (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
    RC τ t I R Z S → ∃ t' S', t' ⋖ t ∧ IS_self τ t' I Z S'

/-- KCI resistance on the responder side. -/
def KCIResistantR (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
    RC τ t I R Z S →
        (∃ t' S', t' ⋖ t ∧ IS_self τ t' I Z S')
      ∨ (∃ t', t' ⋖ t ∧ ALTK τ t' I)

/-- UKS resistance on the responder side: if `R` completes believing `I`
    is the initiator, and some `I'` completes thinking it talks to *some*
    responder using the same session key material `Z`, then `I = I'`.

    Dual of `UKSResistant`, which forces the responder identity. -/
def UKSResistantR (τ : Trace) : Prop :=
  ∀ (I I' R R' : Party) (Z : SessionKeyMat) (S S' : ParamSet) (t t' : Time),
    RC τ t  I  R  Z S  →
    IC τ t' I' R' Z S' →
    I = I'


/-! ## R-side proofs -/

/-- Responder-side entity authentication follows from `InjAgreeR`, provided
    no long-term key reveal occurred.  Symmetric to `entityAuth_of_injAgreeI`. -/
theorem entityAuth_R_of_injAgreeR
    (τ : Trace) (h : InjAgreeR τ)
    (hLTK : ∀ t I, ¬ ALTK τ t I) :
    EntityAuthR τ := by
  intro I R Z S t hRC
  rcases h I R Z S t hRC with ⟨⟨t₁, hIS, hbef⟩, _⟩ | ⟨t₁, hAltk, _⟩
  · exact ⟨t₁, S, hbef, hIS⟩
  · exact (hLTK _ _ hAltk).elim

/-- KCI resistance on the responder side follows from `Table1`'s `injAgreeR`
    row, exactly as `KCI_of_Table1` does for the initiator side. -/
theorem KCI_R_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ) :
    KCIResistantR τ := by
  intro I R Z S t hRC
  have V := Table1 m τ h
  rcases V.injAgreeR I R Z S t hRC with
      ⟨⟨t₁, hIS, hbef⟩, _⟩ | ⟨t₁, hAltk, hbef⟩
  · exact Or.inl ⟨t₁, S, hbef, hIS⟩
  · exact Or.inr ⟨t₁, hbef, hAltk⟩

/-- UKS resistance on the responder side follows from `Table1`'s `impAgreeR`
    row, modulo the symmetric R-side honesty hypotheses (no LTK leak of
    `I`, no Eph leaks for either party).  Mirror of `UKS_of_Table1`. -/
theorem UKS_R_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (hHonest :
      ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
        RC τ t I R Z S →
        (∀ t₀, ¬ ALTK τ t₀ I) ∧
        (∀ t₀, ¬ AEph τ t₀ R Z) ∧
        (∀ t₀, ¬ AEph τ t₀ I Z)) :
    UKSResistantR τ := by
  intro I I' R R' Z S S' t t' hRC hIC
  have V := Table1 m τ h
  have impR := V.impAgreeR I R Z S t hRC
  have hH := hHonest I R Z S t hRC
  rcases impR with
      ⟨huniq, _⟩
    | ⟨t₀, hLTK, _⟩
    | ⟨t₀, hEph⟩
    | ⟨t₀, hEph⟩
  · exact (huniq I' R' S' t' hIC).1
  · exact (hH.1 t₀ hLTK).elim
  · exact (hH.2.1 t₀ hEph).elim
  · exact (hH.2.2 t₀ hEph).elim


/-! ## Full UKS

  `UKSResistant` only forces the believed responder identity, and
  `UKSResistantR` only forces the believed initiator identity.  The paper's
  actual statement of UKS resistance asks both: given any pair of completed
  runs (one by `I`, one by `R`) sharing the same `Z`, both peer identities
  agree.  `UKSFull` captures this.

  `UKSFull` follows directly from `Table1.impAgreeI` (the uniqueness
  conjunct *already* gives both equalities at once), under the initiator-
  side honesty hypotheses needed to discharge `ImpAgreeI`'s long-term-key
  and ephemeral-key escape clauses. -/

/-- Both peer identities are pinned down by the session key material:
    given completed runs `IC τ t I R Z S` and `RC τ t' I' R' Z S'` with the
    same `Z`, we have `I = I' ∧ R = R'`. -/
def UKSFull (τ : Trace) : Prop :=
  ∀ (I I' R R' : Party) (Z : SessionKeyMat) (S S' : ParamSet) (t t' : Time),
    IC τ t  I  R  Z S  →
    RC τ t' I' R' Z S' →
    I = I' ∧ R = R'

/-- `UKSFull` for any honest run.  The proof reads `ImpAgreeI`'s uniqueness
    conjunct off the verified `impAgreeI` row of `Table1`. -/
theorem UKSFull_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (hHonest :
      ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
        IC τ t I R Z S →
        (∀ t₀, ¬ ALTK τ t₀ R) ∧
        (∀ t₀, ¬ AEph τ t₀ R Z) ∧
        (∀ t₀, ¬ AEph τ t₀ I Z)) :
    UKSFull τ := by
  intro I I' R R' Z S S' t t' hIC hRC
  have V := Table1 m τ h
  have impI := V.impAgreeI I R Z S t hIC
  have hH := hHonest I R Z S t hIC
  rcases impI with
      ⟨huniq, _⟩
    | ⟨t₀, hLTK, _⟩
    | ⟨t₀, hEph⟩
    | ⟨t₀, hEph⟩
  · have hh := huniq I' R' S' t' hRC
    exact ⟨hh.1, hh.2.1⟩
  · exact (hH.1 t₀ hLTK).elim
  · exact (hH.2.1 t₀ hEph).elim
  · exact (hH.2.2 t₀ hEph).elim

end EDHOC
