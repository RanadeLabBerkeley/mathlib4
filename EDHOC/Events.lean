/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Trace

/-!
# Event predicates

Convenient `Prop`-valued projections of the seven `Action` constructors,
plus the few derived predicates the security definitions reuse:

* adversary events: `K`, `ALTK`, `AEph` and the example deduction rule
  `K_pair_proj` of §3.2;
* protocol events: `IS / IC / RS / RC`;
* "started run by `R` (resp. `I`), forgetting the believed peer":
  `RS_self`, `IS_self`;
* the disjunction `CompletedRun` used in `PFS` to dodge the Tamarin
  fragment limit;
* the coercion `sk_term : SessionKeyMat → Term` showing `Z` to the
  adversary.

This file is the last common dependency before the security predicates
in `EDHOC.Properties`.
-/

namespace EDHOC

/-! ## Adversary events -/

/-- `K^t(p)` — the adversary knows term `p` at time `t`. -/
def K (τ : Trace) (t : Time) (p : Term) : Prop :=
  τ.evt t (.K p)

/-- `A^t_LTK(A)` — long-term key compromise of `A`. -/
def ALTK (τ : Trace) (t : Time) (A : Party) : Prop :=
  τ.evt t (.ALTK A)

/-- `A^t_Eph(A, Z)` — ephemeral key reveal for `A` in the run with session
    key material `Z`. -/
def AEph (τ : Trace) (t : Time) (A : Party) (Z : SessionKeyMat) : Prop :=
  τ.evt t (.AEph A Z)

/-- The example message-deduction rule of §3.2:

      `∀ t k k'. K^t(⟨k, k'⟩) → K^t(k) ∧ K^t(k')`. -/
axiom K_pair_proj
    (τ : Trace) (t : Time) (k k' : Term) :
    K τ t ⟪k, k'⟫ → K τ t k ∧ K τ t k'


/-! ## Protocol events -/

/-- `I^t_S(I, R, Z, S)` — initiator started. -/
def IS (τ : Trace) (t : Time) (I R : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  τ.evt t (.IS I R Z S)

/-- `I^t_C(I, R, Z, S)` — initiator completed. -/
def IC (τ : Trace) (t : Time) (I R : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  τ.evt t (.IC I R Z S)

/-- `R^t_S(I, R, Z, S)` — responder started. -/
def RS (τ : Trace) (t : Time) (I R : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  τ.evt t (.RS I R Z S)

/-- `R^t_C(I, R, Z, S)` — responder completed. -/
def RC (τ : Trace) (t : Time) (I R : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  τ.evt t (.RC I R Z S)


/-! ## Derived event predicates

  `RS_self R Z S` and `IS_self I Z S` project away the believed peer; the
  paper writes `R^t_S(R, Z, S)` for these.

  `CompletedRun` is the `IC ∨ RC` disjunction used by `PFS`. -/

/-- The `R`-start projection `R^t_S(R, Z, S)` — exists some `I` such that
    `RS τ t I R Z S`. -/
def RS_self (τ : Trace) (t : Time) (R : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  ∃ I, RS τ t I R Z S

/-- The symmetric `I`-start projection `I^t_S(I, Z, S)`. -/
def IS_self (τ : Trace) (t : Time) (I : Party) (Z : SessionKeyMat) (S : ParamSet) : Prop :=
  ∃ R, IS τ t I R Z S

/-- The disjunction `I^t_C(I, R, Z) ∨ R^t_C(I, R, Z)` of §3.2.1.  The paper
    merges this into a single Tamarin action `CompletedRun(u, v, sk)` to
    dodge a quantifier-fragment limit; we keep both faces. -/
def CompletedRun (τ : Trace) (t : Time) (I R : Party) (Z : SessionKeyMat) : Prop :=
  (∃ S, IC τ t I R Z S) ∨ (∃ S, RC τ t I R Z S)


/-! ## Term reflection of the session key material

  `PFS` and Tamarin's `secrecyPFS` express "the adversary knows the session
  key material" as `K^t(Z)`.  Since `K` is `Term`-typed and `Z : SessionKeyMat`,
  we need a coercion. -/

/-- The reflection of the session key material `Z` as a term in the message
    algebra (i.e. how the adversary sees it). -/
axiom sk_term : SessionKeyMat → Term

end EDHOC
