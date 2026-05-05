/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Events

/-!
# Security properties (§3.2.1, §3.2.2)

The five trace predicates verified by Tamarin in Table 1.  Each is a
literal Lean rendering of the formula in Figure 4 of arXiv:2007.11427v3:

* `PFS` — perfect forward secrecy (§3.2.1),
* `InjAgreeI` / `InjAgreeR` — injective agreement on each side (§3.2.2),
* `ImpAgreeI` / `ImpAgreeR` — implicit agreement on each side (§3.2.2).

All five predicates use the *contrapositive* style of the paper: the
positive conclusion sits on one branch of a disjunction, while the other
branches expose the adversary capabilities (LTK / Eph reveal) that would
break it.
-/

namespace EDHOC

/-! ## Perfect forward secrecy (§3.2.1, Figure 4)

  Read negatively: "if the adversary ever learns the session key
  material `Z` of a completed run, then *something* must have leaked":

  > `PFS ≜ ∀ I R Z t₂ t₃.`
  > `K^{t₃}(Z) ∧ (I^{t₂}_C(I, R, Z) ∨ R^{t₂}_C(I, R, Z))`
  > `→ (∃t₁. A^{t₁}_LTK(I) ∧ t₁ ⋖ t₂) ∨ (∃t₁. A^{t₁}_LTK(R) ∧ t₁ ⋖ t₂)`
  > `   ∨ (∃t₁. A^{t₁}_Eph(R, Z))    ∨ (∃t₁. A^{t₁}_Eph(I, Z))` -/

/-- Perfect forward secrecy of trace `τ`. -/
def PFS (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (t₂ t₃ : Time),
    K τ t₃ (sk_term Z) →
    CompletedRun τ t₂ I R Z →
        (∃ t₁, ALTK τ t₁ I ∧ t₁ ⋖ t₂)
      ∨ (∃ t₁, ALTK τ t₁ R ∧ t₁ ⋖ t₂)
      ∨ (∃ t₁, AEph τ t₁ R Z)
      ∨ (∃ t₁, AEph τ t₁ I Z)


/-! ## Injective agreement (§3.2.2, Figure 4)

  `InjAgreeI` reads

  > `∀ I R Z S t₂. I^{t₂}_C(I, R, Z, S) →`
  > `( (∃t₁. R^{t₁}_S(R, Z, S) ∧ t₁ ⋖ t₂) ∧`
  > `  (∀ I' R' t₁'. I^{t₁'}_C(I', R', Z, S) → t₁' .= t₂) )`
  > `∨ (∃t₁. A^{t₁}_LTK(R) ∧ t₁ ⋖ t₂)`

  The first conjunct is Lowe's injectivity (the partner run of `R` is
  unique); the disjunct is the standard long-term-key escape clause. -/

/-- Injective agreement on the initiator side. -/
def InjAgreeI (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t₂ : Time),
    IC τ t₂ I R Z S →
        ( (∃ t₁, RS_self τ t₁ R Z S ∧ t₁ ⋖ t₂)
        ∧ (∀ I' R' (t₁' : Time), IC τ t₁' I' R' Z S → t₁' =ₜ t₂) )
      ∨ (∃ t₁, ALTK τ t₁ R ∧ t₁ ⋖ t₂)

/-- Injective agreement on the responder side (symmetric). -/
def InjAgreeR (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t₂ : Time),
    RC τ t₂ I R Z S →
        ( (∃ t₁, IS_self τ t₁ I Z S ∧ t₁ ⋖ t₂)
        ∧ (∀ I' R' (t₁' : Time), RC τ t₁' I' R' Z S → t₁' =ₜ t₂) )
      ∨ (∃ t₁, ALTK τ t₁ I ∧ t₁ ⋖ t₂)


/-! ## Implicit agreement (§3.2.2, Figure 4)

  Implicit agreement says "anyone who knows `Z` is the intended peer".
  Unlike injective agreement, it does *not* require key confirmation, so
  it picks up additional escape clauses for ephemeral-key reveals. -/

/-- Implicit agreement on the initiator side. -/
def ImpAgreeI (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t₁ : Time),
    IC τ t₁ I R Z S →
          ( ( ∀ I' R' S' (t₂ : Time),
                RC τ t₂ I' R' Z S' → I = I' ∧ R = R' ∧ S = S' )
          ∧ ( ∀ I' R' S' (t₁' : Time),
                IC τ t₁' I' R' Z S' → t₁' =ₜ t₁ ) )
      ∨ (∃ t₀, ALTK τ t₀ R ∧ t₀ ⋖ t₁)
      ∨ (∃ t₀, AEph τ t₀ R Z)
      ∨ (∃ t₀, AEph τ t₀ I Z)

/-- Implicit agreement on the responder side; the paper omits the formula
    but states it is symmetric. -/
def ImpAgreeR (τ : Trace) : Prop :=
  ∀ (I R : Party) (Z : SessionKeyMat) (S : ParamSet) (t₁ : Time),
    RC τ t₁ I R Z S →
          ( ( ∀ I' R' S' (t₂ : Time),
                IC τ t₂ I' R' Z S' → I = I' ∧ R = R' ∧ S = S' )
          ∧ ( ∀ I' R' S' (t₁' : Time),
                RC τ t₁' I' R' Z S' → t₁' =ₜ t₁ ) )
      ∨ (∃ t₀, ALTK τ t₀ I ∧ t₀ ⋖ t₁)
      ∨ (∃ t₀, AEph τ t₀ R Z)
      ∨ (∃ t₀, AEph τ t₀ I Z)

end EDHOC
