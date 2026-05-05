/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Preliminaries

/-!
# Traces and action labels

Multiset rewrite rules in Tamarin produce a *trace* — a partial order of
timestamps each labelled with a multiset of "action facts".  This file
abstracts that machinery into

* `Action`   — the seven action labels Section 3 actually mentions
               (`IS / IC / RS / RC / K / ALTK / AEph`),
* `Trace`    — a single-field record `{ evt : Time → Action → Prop }`,
* `sameKind` — "two actions share their constructor",
* `Trace.uniq_per_type` — the §3.2 axiom that no two actions of the same
                          kind share a timestamp.

The opaque types `ParamSet` (the agreed parameter set, instantiated by
`SP` or `SF` in `EDHOC.AgreedParameters`) and `SessionKeyMat` (the session
key material `Z` of §2.2.3) live here too because `Action` mentions them.
-/

namespace EDHOC

/-! ## Action parameters

  Two opaque types referenced by `Action` constructors.  They are kept
  abstract so that the file does not commit to a representation. -/

/-- The set `S` of agreed parameters (§3.2.3).  `EDHOC.AgreedParameters`
    refines this with the concrete `SP` / `SF` records. -/
axiom ParamSet : Type
/-- A canonical inhabitant of `ParamSet`. -/
axiom ParamSet.default : ParamSet
noncomputable instance : Inhabited ParamSet := ⟨ParamSet.default⟩

/-- The session key material `Z` of §2.2.3.  Always contains `P_e`, plus
    optionally `P_I` and / or `P_R` depending on the EDHOC method. -/
axiom SessionKeyMat : Type
/-- A canonical inhabitant of `SessionKeyMat`. -/
axiom SessionKeyMat.default : SessionKeyMat
noncomputable instance : Inhabited SessionKeyMat := ⟨SessionKeyMat.default⟩


/-! ## Action labels

  The action facts emitted by the rules of §3.4 that Section 3 actually
  references.  Other facts (`Fr`, `KU`, `Out`, …) live in `EDHOC.Tamarin`. -/

/-- An action label emitted by Tamarin rules.  Each constructor corresponds
    to one event type from §3.2 / §3.4. -/
inductive Action
  /-- Initiator started: `I^t_S(I, R, Z, S)`. -/
  | IS  (I R : Party) (Z : SessionKeyMat) (S : ParamSet)
  /-- Initiator completed: `I^t_C(I, R, Z, S)`. -/
  | IC  (I R : Party) (Z : SessionKeyMat) (S : ParamSet)
  /-- Responder started: `R^t_S(I, R, Z, S)`. -/
  | RS  (I R : Party) (Z : SessionKeyMat) (S : ParamSet)
  /-- Responder completed: `R^t_C(I, R, Z, S)`. -/
  | RC  (I R : Party) (Z : SessionKeyMat) (S : ParamSet)
  /-- Adversary knows a term `p`: `K^t(p)`. -/
  | K   (p : Term)
  /-- Adversary learned a party's long-term key: `A^t_LTK(A)`. -/
  | ALTK (A : Party)
  /-- Adversary learned an ephemeral key used to derive `Z`: `A^t_Eph(A, Z)`. -/
  | AEph (A : Party) (Z : SessionKeyMat)

/-- Two actions are *of the same type* iff they share their constructor.
    Used by `Trace.uniq_per_type` to forbid distinct same-kind events at
    a single timestamp. -/
def sameKind : Action → Action → Prop
  | .IS  _ _ _ _, .IS  _ _ _ _ => True
  | .IC  _ _ _ _, .IC  _ _ _ _ => True
  | .RS  _ _ _ _, .RS  _ _ _ _ => True
  | .RC  _ _ _ _, .RC  _ _ _ _ => True
  | .K   _,       .K   _       => True
  | .ALTK _,      .ALTK _      => True
  | .AEph _ _,    .AEph _ _    => True
  | _,            _            => False


/-! ## Traces

  A trace assigns to each timestamp a set of action labels.  Distinct
  timestamps may be incomparable under `⋖`; events of the same kind cannot
  share a timestamp (`Trace.uniq_per_type`).

  The field is named `evt` rather than `at` because `at` is a reserved
  Lean 4 keyword. -/

/-- A trace is a labelling of timestamps by sets of action facts. -/
structure Trace where
  /-- `evt t a` ↔ "action `a` occurred at time `t`". -/
  evt : Time → Action → Prop

/-- Convenience predicate: "action `a` occurs at time `t` in `τ`". -/
def Trace.holds (τ : Trace) (t : Time) (a : Action) : Prop := τ.evt t a

/-- §3.2 axiom: two events of the *same* kind cannot share a timestamp. -/
axiom Trace.uniq_per_type :
    ∀ (τ : Trace) (t : Time) (a₁ a₂ : Action),
      sameKind a₁ a₂ → τ.evt t a₁ → τ.evt t a₂ → a₁ = a₂

end EDHOC
