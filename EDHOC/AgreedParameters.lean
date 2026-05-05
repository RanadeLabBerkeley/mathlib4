/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Trace

/-!
# Agreed-parameter records (§3.2.3)

Section 3.2.3 distinguishes two flavours of agreed-parameter set:

* `S_P` — the *partial* set agreed by both peers in every method.  It pins
  down roles, the responder identity, the session key material `Z`, the
  connection identifiers, and the cipher suite.
* `S_F` — the *full* set, extending `S_P` with the initiator identity and
  (when the initiator uses STAT) the `P_I` component of `Z`.

Two lookup tables in `EDHOC.Table1` decide which flavour is verified for
each method × role: `S_F` for the responder under all methods, `S_P` for
the initiator in the STAT-* methods, `S_F` otherwise.

The records here are coerced into the abstract `ParamSet` type via the
two opaque (and injective) maps `SP_to_paramSet` / `SF_to_paramSet`.
-/

namespace EDHOC

/-! ## Connection identifiers, suites, and `P_I` / `P_R` ingredients

  These are the syntactic ingredients that go into `S_P` and `S_F`. -/

/-- The roles taken by initiator and responder. -/
inductive Role
  | initiator
  | responder
  deriving DecidableEq, Repr

/-- Connection identifier (`C_I` or `C_R`). -/
axiom ConnId : Type
/-- A canonical inhabitant of `ConnId`. -/
axiom ConnId.default : ConnId
noncomputable instance : Inhabited ConnId := ⟨ConnId.default⟩

/-- Cipher suite negotiated by the initiator (the paper's `S_I`). -/
axiom CipherSuiteId : Type
/-- A canonical inhabitant of `CipherSuiteId`. -/
axiom CipherSuiteId.default : CipherSuiteId
noncomputable instance : Inhabited CipherSuiteId := ⟨CipherSuiteId.default⟩

/-- The `P_I` component of the session key material when the initiator
    uses the STAT method. -/
axiom PI_term : Type
/-- A canonical inhabitant of `PI_term`. -/
axiom PI_term.default : PI_term
noncomputable instance : Inhabited PI_term := ⟨PI_term.default⟩

/-- The `P_R` component of the session key material when the responder
    uses the STAT method (mentioned in §3.2.3 / §4.3). -/
axiom PR_term : Type
/-- A canonical inhabitant of `PR_term`. -/
axiom PR_term.default : PR_term
noncomputable instance : Inhabited PR_term := ⟨PR_term.default⟩


/-! ## Partial and full agreed sets -/

/-- The partial agreed-parameter set `S_P` (§3.2.3). -/
structure SP where
  /-- The role played by the calling party. -/
  initRole : Role
  /-- The role played by the believed peer. -/
  peerRole : Role
  /-- Identity of the believed responder. -/
  responder_id : Party
  /-- Established session key material. -/
  Z       : SessionKeyMat
  /-- Initiator's connection identifier. -/
  cI      : ConnId
  /-- Responder's connection identifier. -/
  cR      : ConnId
  /-- Negotiated cipher suite. -/
  suite   : CipherSuiteId

/-- The full agreed-parameter set `S_F = S_P ∪ {I} ∪ {P_I}` (§3.2.3, last
    paragraph). -/
structure SF extends SP where
  /-- Identity of the believed initiator. -/
  initiator_id : Party
  /-- `P_I` is part of the agreed set only when the initiator uses STAT. -/
  pi      : Option PI_term


/-! ## Coercion into the abstract `ParamSet`

  `EDHOC.Trace`'s `ParamSet` is an opaque type referenced by the `Action`
  constructors.  The two maps below witness that `SP` and `SF` faithfully
  embed; injectivity is needed nowhere yet but is recorded for downstream
  consumers. -/

/-- Coercion `SP → ParamSet`. -/
axiom SP_to_paramSet : SP → ParamSet
/-- Coercion `SF → ParamSet`. -/
axiom SF_to_paramSet : SF → ParamSet

/-- The `SP → ParamSet` coercion is injective. -/
axiom SP_to_paramSet_inj : Injective SP_to_paramSet
/-- The `SF → ParamSet` coercion is injective. -/
axiom SF_to_paramSet_inj : Injective SF_to_paramSet

end EDHOC
