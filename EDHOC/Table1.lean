/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Inferred
import EDHOC.AgreedParameters

/-!
# The verified properties (Table 1)

The four columns of Table 1 (SIG-SIG / SIG-STAT / STAT-SIG / STAT-STAT)
list the five rows (`InjAgreeI`, `InjAgreeR`, `ImpAgreeI`, `ImpAgreeR`,
`PFS`) verified by Tamarin.  We:

* enumerate the four EDHOC methods as `Method`;
* record per-method × per-role granularities `S_P` vs `S_F`;
* bundle the five verified rows into `VerifiedTable1`;
* posit the verification result as `axiom Table1`;
* derive the initiator-side inferred corollaries `KCI_of_Table1` and
  `UKS_of_Table1` (§3.2.4).

The responder-side mirrors are proved in `EDHOC.Dual`.
-/

namespace EDHOC

/-! ## The four methods -/

/-- The four EDHOC key-establishment methods analysed in the paper.  The
    naming is `Initiator-Responder` per §2.2.1. -/
inductive Method
  | sigSig
  | sigStat
  | statSig
  | statStat
  deriving DecidableEq, Repr


/-! ## Per-method granularities (Table 1)

  `S_F` is verified for the responder under all methods.  For the
  initiator, Table 1 gives `S_F` for the SIG-* methods and `S_P` for the
  STAT-* methods. -/

/-- Injective-agreement granularity for the initiator: `S_F` for SIG-*,
    `S_P` for STAT-*. -/
def initInjGranularity : Method → Type
  | .sigSig   => SF
  | .sigStat  => SF
  | .statSig  => SP
  | .statStat => SP

/-- Injective-agreement granularity for the responder is uniformly `S_F`
    across all four methods (Table 1, second row). -/
def respInjGranularity (_ : Method) : Type := SF

/-- Implicit-agreement granularity is `S_F` for both roles in all four
    methods (Table 1, rows three and four). -/
def impGranularity (_ : Method) (_ : Role) : Type := SF


/-! ## Honest runs and the verified bundle -/

/-- Predicate "the trace `τ` represents an honest run of method `m`".
    Kept abstract; in Tamarin this is the union of all rules tagged with
    the method name. -/
axiom honestRun : Method → Trace → Prop

/-- The bundle of properties verified by Tamarin for method `m` (Table 1).
    Each conjunct is a Lean transcription of one row. -/
structure VerifiedTable1 (m : Method) (τ : Trace) : Prop where
  /-- Row 5: PFS. -/
  pfs        : PFS τ
  /-- Row 1: injective agreement on the initiator side. -/
  injAgreeI  : InjAgreeI τ
  /-- Row 2: injective agreement on the responder side. -/
  injAgreeR  : InjAgreeR τ
  /-- Row 3: implicit agreement on the initiator side. -/
  impAgreeI  : ImpAgreeI τ
  /-- Row 4: implicit agreement on the responder side. -/
  impAgreeR  : ImpAgreeR τ

/-- §5 / Table 1: every method enjoys the five properties on every honest
    run.  This is the *result* of the Tamarin analysis, posited here as an
    axiom. -/
axiom Table1 :
    ∀ (m : Method) (τ : Trace), honestRun m τ → VerifiedTable1 m τ


/-! ## Initiator-side inferred corollaries (§3.2.4) -/

/-- KCI resistance for every method on every honest run, modulo the
    long-term-key-reveal escape clause.  Follows from `injAgreeI` (Row 1
    of Table 1). -/
theorem KCI_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ) :
    KCIResistant τ := by
  intro I R Z S t hIC
  have V := Table1 m τ h
  rcases V.injAgreeI I R Z S t hIC with
      ⟨⟨t₁, hRS, hbef⟩, _⟩ | ⟨t₁, hAltk, hbef⟩
  · exact Or.inl ⟨t₁, S, hbef, hRS⟩
  · exact Or.inr ⟨t₁, hbef, hAltk⟩

/-- UKS resistance: `ImpAgreeI` (Row 3 of Table 1) directly forces the
    responder identity once its escape clauses are closed. -/
theorem UKS_of_Table1
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (hHonest :
      ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t : Time),
        IC τ t I R Z S →
        (∀ t₀, ¬ ALTK τ t₀ R) ∧
        (∀ t₀, ¬ AEph τ t₀ R Z) ∧
        (∀ t₀, ¬ AEph τ t₀ I Z)) :
    UKSResistant τ := by
  intro I R R' Z S S' t t' hIC hRC
  have V := Table1 m τ h
  have impI := V.impAgreeI I R Z S t hIC
  have hH := hHonest I R Z S t hIC
  rcases impI with
      ⟨huniq, _⟩
    | ⟨t₀, hLTK, _⟩
    | ⟨t₀, hEph⟩
    | ⟨t₀, hEph⟩
  · -- The uniqueness conjunct of `ImpAgreeI` directly gives `R = R'`.
    have := huniq I R' S' t' hRC
    exact this.2.1
  · exact (hH.1 t₀ hLTK).elim
  · exact (hH.2.1 t₀ hEph).elim
  · exact (hH.2.2 t₀ hEph).elim

end EDHOC
