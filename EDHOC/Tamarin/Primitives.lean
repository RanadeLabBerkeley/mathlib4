/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Tamarin.Framework

/-!
# Tamarin: primitive operations (§3.4.1)

Cryptographic primitives used by the EDHOC rules: AEAD, signatures, hash,
HKDF, Diffie–Hellman, XOR.  Each primitive is a function symbol with the
defining equation Tamarin expects (e.g. `aeadDecrypt (aeadEncrypt …) … = …`).

These are postulated as `axiom`s rather than `def`s because Section 3 is
parametric in the underlying constructions.

We also encode one Dolev–Yao deduction rule explicitly — the rule from
§3.4.1 that lets the adversary construct AEAD ciphertexts from known
ingredients — to demonstrate how the `Rule` record is meant to be used.
-/

namespace EDHOC.Tamarin.Prim

open EDHOC.Tamarin

/-! ## AEAD -/

/-- AEAD encryption `aeadEncrypt(k, m, ad, ai)`. -/
axiom aeadEncrypt : Term → Term → Term → Term → Term

/-- AEAD decryption *with* integrity check; satisfies
    `aeadDecrypt (aeadEncrypt k m ad ai) k ad ai = m`. -/
axiom aeadDecrypt : Term → Term → Term → Term → Term

/-- The AEAD decryption equation. -/
axiom aeadDecrypt_correct (m k ad ai : Term) :
    aeadDecrypt (aeadEncrypt k m ad ai) k ad ai = m

/-- AEAD decryption *without* integrity check, used only by the Dolev–Yao
    adversary (§3.4.1).  Honest parties never call it. -/
axiom decrypt : Term → Term → Term → Term

/-- The unauthenticated-decryption equation. -/
axiom decrypt_correct (m k ad ai : Term) :
    decrypt (aeadEncrypt k m ad ai) k ai = m


/-! ## Signatures -/

/-- Signature operation `sign(m, sk)`. -/
axiom sign   : Term → Term → Term
/-- Signature verification `verify(σ, m, pk)`. -/
axiom verify : Term → Term → Term → Term
/-- The successful-verification constant returned by `verify`. -/
axiom signTrue : Term

/-- The signature/verification equation: `verify (sign m sk) m pk = signTrue`
    (when `pk` matches `sk`). -/
axiom verify_correct (m sk pk : Term) :
    verify (sign m sk) m pk = signTrue


/-! ## HKDF and hash -/

/-- HKDF-Expand. -/
axiom expa : Term → Term → Term
/-- HKDF-Extract. -/
axiom extr : Term → Term → Term

/-- Hash function (§3.4.1) parameterised by a public algorithm constant. -/
axiom hash : Term → Term → Term


/-! ## Diffie–Hellman -/

/-- The DH generator constant `g`. -/
axiom gen   : Term
/-- The DH operation `expg b e = b^e`. -/
axiom expg  : Term → Term → Term

/-- The Diffie–Hellman commutativity equation `(g^x)^y = (g^y)^x`. -/
axiom expg_comm (b e₁ e₂ : Term) :
    expg (expg b e₁) e₂ = expg (expg b e₂) e₁


/-! ## XOR -/

/-- Exclusive-or. -/
axiom XOR     : Term → Term → Term
/-- XOR is commutative. -/
axiom XOR_comm  (a b : Term) : XOR a b = XOR b a
/-- XOR is associative. -/
axiom XOR_assoc (a b c : Term) : XOR (XOR a b) c = XOR a (XOR b c)


/-! ## Sample deduction rule

  The "adversary can construct an AEAD ciphertext" rule of §3.4.1:

    `[!KU(k), !KU(m), !KU(ad), !KU(ai)] --[]-> [!KU(aeadEncrypt(k, m, ad, ai))]`

  Provided as a small showcase of how to use the `Rule` record. -/

/-- The AEAD construction rule, as a `Rule`. -/
noncomputable def aeadCtorRule (k m ad ai : Term) : Rule :=
  { name    := "AEAD-construct"
    lhs     := [.KU k, .KU m, .KU ad, .KU ai]
    actions := []
    rhs     := [.KU (aeadEncrypt k m ad ai)] }

end EDHOC.Tamarin.Prim
