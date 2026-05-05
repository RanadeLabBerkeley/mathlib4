/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Tamarin.Environment

/-!
# Tamarin: protocol roles (§3.4.3)

Each EDHOC method is implemented by four rules `I1 / R2 / I3 / R4`,
corresponding to the event types `IS / RS / IC / RC`.  The paper lists
all sixteen rules across the four methods; we transcribe a
representative one — `R2_STAT_SIG`, the listing on lines 871–911 of the
paper — to demonstrate the encoding.

Variable names are kept identical to the paper.  The function symbols
referenced (`expg`, `extr`, `expa`, `aeadEncrypt`, `sign`, `XOR`, …) all
live in `EDHOC.Tamarin.Prim`.
-/

namespace EDHOC.Tamarin.Roles

open EDHOC.Tamarin EDHOC.Tamarin.Prim EDHOC.Tamarin.Env

/-! ## R2 actions

  Two action labels emitted by `R2_STAT_SIG`. -/

/-- The action `ExpRunningR(˜tid, $V, exp_sk, agreed)` of §3.4.3.  It
    implements the `RS` event with the *explicit* (non-`PI`) flavour of
    the session key material. -/
axiom ExpRunningR :
    Term → Party → SessionKeyMat → ParamSet → Action

/-- The binding action `R2(˜tid, $V, m1, m2)` linking the rule to its
    inputs and outputs. -/
axiom R2act : Term → Party → Term → Term → Action


/-! ## The rule `R2_STAT_SIG`

  The listing on lines 871–911 of the paper.  Free variables:

  * `$V`        — the responder identity,
  * `˜ltk`      — the responder's long-term signature key,
  * `˜CR`       — the responder's choice of connection id,
  * `˜yy`       — the responder's ephemeral DH scalar,
  * `˜tid`      — a unique thread id for this run,
  * `xx`        — the initiator's ephemeral DH scalar (in `gx`),
  * `CS0`       — the negotiated cipher-suite identifier,
  * `CI`        — the initiator's connection id,
  * `$H0`       — the public hash-algorithm constant,
  * `$cAEAD0`   — the public AEAD-algorithm constant. -/
noncomputable def R2_STAT_SIG
    (V : Party) (ltk : Key) (CR yy tid : Term) (xx : Term)
    (CS0 CI H0 cAEAD0 : Term) (pkV : Term) : Rule :=
  let agreed       := ⟪CS0, ⟪CI, CR⟫⟫
  let gx           := expg gen xx
  let data_2       := ⟪expg gen yy, ⟪CI, CR⟫⟫
  let m1           := ⟪H0, ⟪CS0, ⟪CI, gx⟫⟫⟫
  let TH_2         := hash H0 (⟪H0, ⟪m1, data_2⟫⟫)
  let prk_2e       := extr H0 (expg gx yy)
  let prk_3e2m     := prk_2e
  let K_2m         := expa (⟪cAEAD0, ⟪TH_2, H0⟫⟫) prk_3e2m
  let protected2   := Party.toTerm V
  let CRED_V       := pkV
  let extAad2      := ⟪TH_2, CRED_V⟫
  let assocData2   := ⟪protected2, extAad2⟫
  let MAC_2        := aeadEncrypt H0 K_2m assocData2 cAEAD0
  let authV        := sign (⟪assocData2, MAC_2⟫) (Key.toTerm ltk)
  let plainText2   := ⟪Party.toTerm V, authV⟫
  let K_2e         := expa (⟪cAEAD0, ⟪TH_2, H0⟫⟫) prk_2e
  let K_2e_1       := expa (⟪cAEAD0, ⟪TH_2, ⟪H0, gen⟫⟫⟫) prk_2e
  let K_2e_2       := expa (⟪cAEAD0, ⟪TH_2, ⟪H0, expg gen gen⟫⟫⟫) prk_2e
  let CIPHERTEXT_2 := ⟪XOR (Party.toTerm V) K_2e_1, XOR authV K_2e_2⟫
  let m2           := ⟪data_2, CIPHERTEXT_2⟫
  let exp_sk_term  := expg gx yy
  let exp_sk : SessionKeyMat := SessionKeyMat.default
  let agreedSet : ParamSet := ParamSet.default
  -- Silence unused-let warnings (the values are kept for traceability).
  let _ := plainText2
  let _ := m1
  let _ := K_2e
  let _ := exp_sk_term
  { name    := "R2_STAT_SIG"
    lhs     := [ .LTK_SIG V ltk
               , .PK_SIG  V pkV
               , .In  m1
               , .Fr  CR
               , .Fr  yy
               , .Fr  tid ]
    actions := [ ExpRunningR tid V exp_sk agreedSet
               , R2act tid V m1 m2 ]
    rhs     := [ .State "StR2_STAT_SIG"
                  [ Party.toTerm V
                  , Key.toTerm ltk
                  , yy
                  , H0
                  , TH_2
                  , CIPHERTEXT_2
                  , expg gx yy
                  , tid
                  , m1
                  , m2
                  , agreed ]
               , .Out m2 ] }

end EDHOC.Tamarin.Roles
