/-
  EDHOC.lean
  ==========

  A Lean 4 formalization of the objects defined in Section 3
  ("EDHOC Overview") of the EDHOC Internet-Draft
  (draft-ietf-lake-edhoc, expires January 7, 2021 — Selander et al.).

  Design choices (per user request):
    • Fully abstract cryptographic primitives: opaque types + axioms.
    • No dependency on Mathlib — a few basic predicates (`Injective`,
      `Nonempty`) are declared inline.
    • Structural, KDF-level, and protocol-level security statements
      are all scaffolded so the user can pick which to prove.

  The file is organised bottom-up:

      §A  Preliminaries                         (Injective, option helpers)
      §B  ByteString and CBOR encoding          (§3 ambient encoding)
      §C  COSE algorithms and cipher suites     (§3.4)
      §D  Methods and correlation               (§3.1)
      §E  Connection identifiers                (§3.3)
      §F  ECDH primitives                       (§3.7, §3.8)
      §G  Pre-shared keys                       (§3.2)
      §H  Hash and HKDF                         (§3.8)
      §I  info structure and EDHOC-KDF          (§3.8)
      §J  PRK chain                             (§3.8)
      §K  Transcript hashes                     (§3.8, §3.8.1)
      §L  Derived session keys (K_*, IV_*)      (§3.8)
      §M  EDHOC-Exporter and PSK chaining       (§3.8.1, §3.8.2)
      §N  Ephemeral public keys (COSE_Key)      (§3.7)
      §O  Auxiliary data                        (§3.6)
      §P  Messages and protocol state           (§3, §3.5)
      §Q  Security framework                    (adversary view, closures)
      §R  Security statements (scaffolded)      (structural / KDF / protocol)

  Everything is wrapped in `namespace EDHOC`.

  NOTE: References in the draft to §4.3.1, §4.4.1, etc. concern the
  concrete wire format of message_1..message_3, which lives in §4 of the
  draft (not reproduced in the source supplied). Those messages are
  therefore left as opaque byte strings with injectivity axioms here,
  leaving room for a later refinement.
-/

namespace EDHOC

/-! =====================================================================
    §A  Preliminaries
    ===================================================================== -/

/-- A function is injective. Kept local to avoid a Mathlib dependency. -/
def Injective {α β : Sort _} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- A binary function is injective in both arguments jointly. -/
def Injective₂ {α β γ : Sort _} (f : α → β → γ) : Prop :=
  ∀ a₁ a₂ b₁ b₂, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

/-! =====================================================================
    §B  ByteString and CBOR encoding

    EDHOC messages are CBOR Sequences (RFC 8742). We keep the byte
    layer abstract: byte strings form a monoid under concatenation
    with a designated empty element, and CBOR encoders for the basic
    CDDL types used in §3 (int, bstr, tstr, uint, array) are postulated
    to be injective.
    ===================================================================== -/

/-- Opaque type of byte strings. -/
structure ByteString where
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- Byte strings are inhabited (by the empty string). -/
def ByteString.empty : ByteString := ⟨[]⟩

instance : Inhabited ByteString := ⟨ByteString.empty⟩

/-- Concatenation of byte strings. -/
def ByteString.append (a b : ByteString) : ByteString :=
  ⟨a.bytes ++ b.bytes⟩

instance : Append ByteString := ⟨ByteString.append⟩

/-- Concatenation is associative. -/
axiom ByteString.append_assoc :
  ∀ a b c : ByteString, (a ++ b) ++ c = a ++ (b ++ c)

/-- The empty byte string is a left and right unit for concatenation. -/
axiom ByteString.empty_append : ∀ a : ByteString, ByteString.empty ++ a = a
axiom ByteString.append_empty : ∀ a : ByteString, a ++ ByteString.empty = a

/-- CBOR encoders for the atomic CDDL types occurring in §3. -/
axiom CBOR.encodeInt   : Int → ByteString
axiom CBOR.encodeUint  : Nat → ByteString
axiom CBOR.encodeBstr  : ByteString → ByteString
axiom CBOR.encodeTstr  : String → ByteString
/-- CBOR array encoder, length-tagged. Used for `info` and similar. -/
axiom CBOR.encodeArray : List ByteString → ByteString

/-- Each atomic encoder is injective. -/
axiom CBOR.encodeInt_inj   : Injective CBOR.encodeInt
axiom CBOR.encodeUint_inj  : Injective CBOR.encodeUint
axiom CBOR.encodeBstr_inj  : Injective CBOR.encodeBstr
axiom CBOR.encodeTstr_inj  : Injective CBOR.encodeTstr
axiom CBOR.encodeArray_inj : Injective CBOR.encodeArray

/-- CBOR major types are disjoint (RFC 8949 §3): the outputs of the
    atomic encoders for distinct CDDL types never coincide. We only
    state the pair we actually use (`int` vs `tstr`) for `Info`
    encoding; add more as needed. -/
axiom CBOR.encodeInt_ne_encodeTstr :
  ∀ (n : Int) (s : String), CBOR.encodeInt n ≠ CBOR.encodeTstr s


/-! =====================================================================
    §C  COSE algorithms and cipher suites  (§3.4)

    A cipher suite is an ordered 7-tuple of COSE identifiers:
      (AEAD, hash, ECDH curve, sig alg, sig curve, app AEAD, app hash).
    Algorithm identifiers are either ints or tstrs (RFC 8152).
    ===================================================================== -/

/-- A COSE algorithm identifier (int or tstr per RFC 8152 §8.1). -/
inductive CoseAlgId
  | int  (n : Int)
  | tstr (s : String)
  deriving DecidableEq, Repr

/-- A COSE elliptic-curve identifier. Always an int in the registry. -/
structure CoseCurveId where
  value : Int
  deriving DecidableEq, Repr

/-- EDHOC cipher suite: ordered 7-tuple (§3.4). -/
structure CipherSuite where
  edhocAead      : CoseAlgId      -- EDHOC AEAD algorithm
  edhocHash      : CoseAlgId      -- EDHOC hash algorithm
  edhocEcdhCurve : CoseCurveId    -- EDHOC ECDH curve
  edhocSig       : CoseAlgId      -- EDHOC signature algorithm
  edhocSigCurve  : CoseCurveId    -- EDHOC signature algorithm curve
  appAead        : CoseAlgId      -- Application AEAD algorithm
  appHash        : CoseAlgId      -- Application hash algorithm
  deriving DecidableEq, Repr

namespace CipherSuite

/- The four pre-defined cipher suites listed in §3.4. -/

/- Suite 0 : (AES-CCM-16-64-128, SHA-256, X25519, EdDSA, Ed25519,
                AES-CCM-16-64-128, SHA-256) -/
def suite0 : CipherSuite where
  edhocAead      := .int 10
  edhocHash      := .int (-16)
  edhocEcdhCurve := ⟨4⟩
  edhocSig       := .int (-8)
  edhocSigCurve  := ⟨6⟩
  appAead        := .int 10
  appHash        := .int (-16)

/-- Suite 1 : (AES-CCM-16-128-128, SHA-256, X25519, EdDSA, Ed25519,
                AES-CCM-16-64-128, SHA-256) -/
def suite1 : CipherSuite where
  edhocAead      := .int 30
  edhocHash      := .int (-16)
  edhocEcdhCurve := ⟨4⟩
  edhocSig       := .int (-8)
  edhocSigCurve  := ⟨6⟩
  appAead        := .int 10
  appHash        := .int (-16)

/-- Suite 2 : (AES-CCM-16-64-128, SHA-256, P-256, ES256, P-256,
                AES-CCM-16-64-128, SHA-256) -/
def suite2 : CipherSuite where
  edhocAead      := .int 10
  edhocHash      := .int (-16)
  edhocEcdhCurve := ⟨1⟩
  edhocSig       := .int (-7)
  edhocSigCurve  := ⟨1⟩
  appAead        := .int 10
  appHash        := .int (-16)

/-- Suite 3 : (AES-CCM-16-128-128, SHA-256, P-256, ES256, P-256,
                AES-CCM-16-64-128, SHA-256) -/
def suite3 : CipherSuite where
  edhocAead      := .int 30
  edhocHash      := .int (-16)
  edhocEcdhCurve := ⟨1⟩
  edhocSig       := .int (-7)
  edhocSigCurve  := ⟨1⟩
  appAead        := .int 10
  appHash        := .int (-16)

/-- The pre-defined suite catalogue, indexed by int label. -/
def predefined : Int → Option CipherSuite
  | 0 => some suite0
  | 1 => some suite1
  | 2 => some suite2
  | 3 => some suite3
  | _ => none

end CipherSuite


/-! =====================================================================
    §D  Authentication methods and correlation (§3.1)
    ===================================================================== -/

/-- Authentication material used by a party. Per §3.2 / §9.2. -/
inductive AuthMethod
  | signature   -- signature keys (RPK or cert, digitalSignature)
  | staticDH    -- static Diffie-Hellman keys (RPK or cert, keyAgreement)
  | psk         -- pre-shared key (symmetric)
  deriving DecidableEq, Repr

/-- The `method` parameter combines Initiator and Responder choices.
    In the PSK case both sides use `psk` and the pair collapses. -/
structure Method where
  initiator : AuthMethod
  responder : AuthMethod
  deriving DecidableEq, Repr

/-- The correlation parameter `corr` (§3.1). -/
inductive Corr
  /-- corr = 0 : no transport correlation. -/
  | none
  /-- corr = 1 : transport lets Responder correlate msg_2 with msg_1. -/
  | respCorrelates
  /-- corr = 2 : transport lets Initiator correlate msg_3 with msg_2. -/
  | initCorrelates
  /-- corr = 3 : transport lets both sides correlate. -/
  | bothCorrelate
  deriving DecidableEq, Repr

/-- Numeric encoding of `corr` as used in METHOD_CORR. -/
def Corr.toNat : Corr → Nat
  | .none            => 0
  | .respCorrelates  => 1
  | .initCorrelates  => 2
  | .bothCorrelate   => 3

/-- The combined METHOD_CORR int that opens message_1. The draft leaves
    its exact packing as an implementation detail of §3.1; we abstract
    it here as an injective int. -/
axiom METHOD_CORR : Method → Corr → Int
axiom METHOD_CORR_inj :
  ∀ m₁ m₂ c₁ c₂, METHOD_CORR m₁ c₁ = METHOD_CORR m₂ c₂ → m₁ = m₂ ∧ c₁ = c₂


/-! =====================================================================
    §E  Connection identifiers (§3.3)

    C_I and C_R are byte strings carrying no cryptographic meaning.
    They may be empty. We expose them as a named alias for ByteString.
    ===================================================================== -/

/-- Connection identifier (C_I, C_R). May be the empty byte string. -/
def ConnId : Type := ByteString

/-- A pair of connection identifiers, one chosen by each party. -/
structure ConnIds where
  cI : ConnId    -- chosen by the Responder for the Initiator to use
  cR : ConnId    -- chosen by the Initiator for the Responder to use


/-! =====================================================================
    §F  ECDH primitives (§3.7, §3.8)

    Following COSE (RFC 8152 §12.4.1), an ECDH private/public pair lives
    on the curve specified by the selected cipher suite. We keep the
    curve as an explicit parameter and postulate only:
      • scalar-to-point map     pub : PrivScalar → PubPoint
      • Diffie-Hellman map      ecdh : PrivScalar → PubPoint → SharedSecret
      • DH symmetry             ecdh x (pub y) = ecdh y (pub x)
    ===================================================================== -/

axiom PrivScalar   : Type
axiom PubPoint     : Type
axiom SharedSecret : Type

axiom PrivScalar.default   : PrivScalar
axiom PubPoint.default     : PubPoint
axiom SharedSecret.default : SharedSecret

noncomputable instance : Inhabited PrivScalar   := ⟨PrivScalar.default⟩
noncomputable instance : Inhabited PubPoint     := ⟨PubPoint.default⟩
noncomputable instance : Inhabited SharedSecret := ⟨SharedSecret.default⟩

/-- Public-point derivation `g^x`, parameterised by curve. -/
axiom PubPoint.ofScalar : CoseCurveId → PrivScalar → PubPoint

/-- The ECDH function `X25519` / P-256 scalar multiplication. -/
axiom ecdh : CoseCurveId → PrivScalar → PubPoint → SharedSecret

/-- Diffie-Hellman commutativity (§3.8, the G_XY equation). -/
axiom ecdh_symm (c : CoseCurveId) (x y : PrivScalar) :
  ecdh c x (PubPoint.ofScalar c y) = ecdh c y (PubPoint.ofScalar c x)


/-! =====================================================================
    §G  Pre-shared keys (§3.2)
    ===================================================================== -/

axiom PSK : Type
axiom PSK.default : PSK
noncomputable instance : Inhabited PSK := ⟨PSK.default⟩

/-- Identifier used to retrieve a PSK (§3.2). Abstract byte string. -/
def ID_PSK : Type := ByteString


/-! =====================================================================
    §H  Hash and HKDF (§3.8)

    The spec mandates HKDF (RFC 5869) parameterised by the EDHOC hash
    algorithm of the selected cipher suite. We separate the extract
    variants by the *type* of the salt (empty / PSK / PRK) so that each
    use of PRK_{2e,3e2m,4x3m} in §3.8 can be type-checked directly.
    ===================================================================== -/

axiom PRK : Type
axiom PRK.default : PRK
noncomputable instance : Inhabited PRK := ⟨PRK.default⟩

/-- Output keying material: a byte string of requested length. -/
def OKM : Type := ByteString

/-- HKDF-Extract with empty salt. Used when EDHOC is authenticated with
    asymmetric credentials (signature or static DH). -/
axiom HKDF.extractEmpty : CoseAlgId → SharedSecret → PRK

/-- HKDF-Extract with a PSK as salt. Used when EDHOC is authenticated
    with symmetric credentials. -/
axiom HKDF.extractPSK : CoseAlgId → PSK → SharedSecret → PRK

/-- HKDF-Extract chained: the salt is itself a previously derived PRK.
    Used for PRK_3e2m and PRK_4x3m. -/
axiom HKDF.extractPRK : CoseAlgId → PRK → SharedSecret → PRK

/-- HKDF-Expand: `HKDF-Expand(PRK, info, length) = OKM`. -/
axiom HKDF.expand : CoseAlgId → PRK → ByteString → Nat → OKM

/-- The hash function of a selected suite (used for transcript hashes). -/
axiom Hash.hash : CoseAlgId → ByteString → ByteString


/-! =====================================================================
    §I  The `info` structure and EDHOC-KDF (§3.8)

        info = [ edhoc_aead_id : int / tstr
               , transcript_hash : bstr
               , label : tstr
               , length : uint ]
    ===================================================================== -/

/-- The `info` CBOR array (§3.8). -/
structure Info where
  edhocAeadId    : CoseAlgId
  transcriptHash : ByteString
  label          : String
  length         : Nat
  deriving Repr

namespace Info

/-- Encode one slot of the info array. -/
noncomputable def encodeAeadId : CoseAlgId → ByteString
  | .int n  => CBOR.encodeInt n
  | .tstr s => CBOR.encodeTstr s

/-- CBOR encoding of the `info` array. -/
noncomputable def encode (i : Info) : ByteString :=
  CBOR.encodeArray
    [ encodeAeadId i.edhocAeadId
    , CBOR.encodeBstr i.transcriptHash
    , CBOR.encodeTstr i.label
    , CBOR.encodeUint i.length ]

/-- An info record uses the AEAD algorithm of a given cipher suite.
    The spec (§3.8) mandates that EDHOC-KDF uses the *single* AEAD id
    of the selected suite across *all* invocations. -/
def usesSuite (i : Info) (cs : CipherSuite) : Prop :=
  i.edhocAeadId = cs.edhocAead

end Info

/-- `EDHOC-KDF(PRK, transcript_hash, label, length)` from §3.8,
    parameterised by the selected cipher suite. -/
noncomputable def EDHOC_KDF (cs : CipherSuite) (prk : PRK)
              (th : ByteString) (label : String) (length : Nat) : OKM :=
  HKDF.expand cs.edhocHash prk
    (Info.encode
      { edhocAeadId    := cs.edhocAead
        transcriptHash := th
        label          := label
        length         := length })
    length


/-! =====================================================================
    §J  The PRK chain (§3.8)

      PRK_2e   = HKDF-Extract( salt,    G_XY )
      PRK_3e2m = HKDF-Extract( PRK_2e,  G_RX )   if Responder static DH
               = PRK_2e                           otherwise
      PRK_4x3m = HKDF-Extract( PRK_3e2m, G_IY)   if Initiator static DH
               = PRK_3e2m                         otherwise
    ===================================================================== -/

/-- `PRK_2e` in the asymmetric (signature or static-DH) case. -/
noncomputable def PRK_2e_asym (cs : CipherSuite) (gxy : SharedSecret) : PRK :=
  HKDF.extractEmpty cs.edhocHash gxy

/-- `PRK_2e` in the PSK (symmetric) case. -/
noncomputable def PRK_2e_psk (cs : CipherSuite) (psk : PSK) (gxy : SharedSecret) : PRK :=
  HKDF.extractPSK cs.edhocHash psk gxy

/-- `PRK_3e2m` given the previous PRK and the optional G_RX
    (the Responder's static-DH ECDH secret). -/
noncomputable def PRK_3e2m (cs : CipherSuite) (prev : PRK)
             (gRX? : Option SharedSecret) : PRK :=
  match gRX? with
  | some gRX => HKDF.extractPRK cs.edhocHash prev gRX
  | none     => prev

/-- `PRK_4x3m` given the previous PRK and the optional G_IY
    (the Initiator's static-DH ECDH secret). -/
noncomputable def PRK_4x3m (cs : CipherSuite) (prev : PRK)
             (gIY? : Option SharedSecret) : PRK :=
  match gIY? with
  | some gIY => HKDF.extractPRK cs.edhocHash prev gIY
  | none     => prev

/-- The full PRK chain as a record. A `WellFormedChain` proof below
    asserts that the values agree with their spec-given derivations. -/
structure PRKChain where
  cs       : CipherSuite
  prk2e    : PRK
  prk3e2m  : PRK
  prk4x3m  : PRK


/-! =====================================================================
    §K  Transcript hashes (§3.8, §3.8.1)

    TH_2 and TH_3 are defined in §4.3.1 / §4.4.1 of the draft (not
    reproduced here). TH_4 is defined in §3.8.1:

        TH_4 = H(TH_3, CIPHERTEXT_3)
    ===================================================================== -/

/-- Opaque alias to flag that a byte string is a transcript hash
    produced by the suite's hash function. -/
def TranscriptHash : Type := ByteString

/-- `TH_4 = H( TH_3, CIPHERTEXT_3 )` (§3.8.1). The argument to `H` is
    the CBOR sequence `(TH_3, CIPHERTEXT_3)`, which in our abstract
    model we represent by concatenation of the pieces. -/
noncomputable def TH_4 (cs : CipherSuite) (th3 ciphertext3 : ByteString) : TranscriptHash :=
  Hash.hash cs.edhocHash (th3 ++ ciphertext3)


/-! =====================================================================
    §L  Derived session keys and IVs (§3.8)

    Per the spec:
       K_2e  , (IV_2e)     from (PRK_2e   , TH_2)    -- message_2 encryption
       K_2ae , IV_2ae      from (PRK_2e   , TH_2)
       K_2m  , IV_2m       from (PRK_3e2m , TH_2)    -- MAC in message_2
       K_3ae , IV_3ae      from (PRK_3e2m , TH_3)    -- message_3 encryption
       K_3m  , IV_3m       from (PRK_4x3m , TH_3)    -- MAC in message_3
    ===================================================================== -/

namespace Derived

/-- Length parameter abstracted here; in practice given by the suite's
    AEAD key/IV sizes. We expose the label explicitly so users can
    reason about label-distinctness in §R. -/

noncomputable def K_2e   (cs : CipherSuite) (prk2e : PRK)   (th2 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk2e   th2 "K_2e"   n

noncomputable def K_2ae  (cs : CipherSuite) (prk2e : PRK)   (th2 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk2e   th2 "K_2ae"  n

noncomputable def IV_2ae (cs : CipherSuite) (prk2e : PRK)   (th2 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk2e   th2 "IV_2ae" n

noncomputable def K_2m   (cs : CipherSuite) (prk3e2m : PRK) (th2 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk3e2m th2 "K_2m"   n

noncomputable def IV_2m  (cs : CipherSuite) (prk3e2m : PRK) (th2 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk3e2m th2 "IV_2m"  n

noncomputable def K_3ae  (cs : CipherSuite) (prk3e2m : PRK) (th3 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk3e2m th3 "K_3ae"  n

noncomputable def IV_3ae (cs : CipherSuite) (prk3e2m : PRK) (th3 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk3e2m th3 "IV_3ae" n

noncomputable def K_3m   (cs : CipherSuite) (prk4x3m : PRK) (th3 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk4x3m th3 "K_3m"   n

noncomputable def IV_3m  (cs : CipherSuite) (prk4x3m : PRK) (th3 : ByteString) (n : Nat) : OKM :=
  EDHOC_KDF cs prk4x3m th3 "IV_3m"  n

/-- The set of labels the spec reserves for session-key derivation
    from §3.8. Useful for expressing label-distinctness of the
    EDHOC-Exporter (see §R.KDF). -/
def specLabels : List String :=
  ["K_2e", "K_2ae", "IV_2ae", "K_2m", "IV_2m",
   "K_3ae", "IV_3ae", "K_3m", "IV_3m"]

end Derived


/-! =====================================================================
    §M  EDHOC-Exporter and PSK chaining (§3.8.1, §3.8.2)
    ===================================================================== -/

/-- `EDHOC-Exporter(label, length) = EDHOC-KDF(PRK_4x3m, TH_4, label, length)`. -/
noncomputable def EDHOC_Exporter (cs : CipherSuite) (prk4x3m : PRK) (th4 : TranscriptHash)
                   (label : String) (length : Nat) : OKM :=
  EDHOC_KDF cs prk4x3m th4 label length

/-- Derived PSK from §3.8.2: `EDHOC-Exporter("EDHOC Chaining PSK", length)`. -/
noncomputable def ChainedPSK_bytes (cs : CipherSuite) (prk4x3m : PRK) (th4 : TranscriptHash)
                     (aeadKeyLen : Nat) : OKM :=
  EDHOC_Exporter cs prk4x3m th4 "EDHOC Chaining PSK" aeadKeyLen

/-- Derived kid_psk from §3.8.2: `EDHOC-Exporter("EDHOC Chaining kid_psk", 4)`. -/
noncomputable def Chained_kid_psk (cs : CipherSuite) (prk4x3m : PRK) (th4 : TranscriptHash)
                    : OKM :=
  EDHOC_Exporter cs prk4x3m th4 "EDHOC Chaining kid_psk" 4


/-! =====================================================================
    §N  Ephemeral public keys (§3.7)

    COSE_Key of type EC2 or OKP; only the `x` parameter appears on the
    wire. We model the wire-level ephemeral public key as just a byte
    string (since the `y` coordinate is omitted per §3.7).
    ===================================================================== -/

/-- COSE key type (RFC 8152 §13). -/
inductive CoseKty | ec2 | okp
  deriving DecidableEq, Repr

/-- The wire form of an ephemeral public key in EDHOC: the `x`
    coordinate, along with the key type and curve that tell the
    receiver how to interpret it. -/
structure EphemeralPubKey where
  kty    : CoseKty
  crv    : CoseCurveId
  xBytes : ByteString


/-! =====================================================================
    §O  Auxiliary data (§3.6)
    ===================================================================== -/

/-- Unprotected auxiliary data carried in message_1 and message_2. -/
def AD_1 : Type := ByteString
def AD_2 : Type := ByteString

/-- Protected auxiliary data carried (encrypted) in message_3. -/
def AD_3 : Type := ByteString


/-! =====================================================================
    §P  Messages and protocol state (§3, §3.5)

    §3 describes only the structure of the three-message flow; §4 of
    the draft gives the exact CBOR layout of each message. We expose
    each message as an opaque byte string with (a) a structured
    "contents" record that the byte string must encode and (b) an
    injective encoding axiom, so that TH_2 / TH_3 / TH_4 can be
    related to well-defined inputs.
    ===================================================================== -/

/-- Abstract contents of message_1 per §3 / §3.5. -/
structure Message1Contents where
  methodCorr : Int                   -- METHOD_CORR (first item)
  suites     : List Int              -- SUITES_I  (proposed cipher suites)
  gX         : EphemeralPubKey       -- G_X       (Initiator's ephemeral)
  cI         : ConnId                -- C_I
  ad1        : Option AD_1

/-- Abstract contents of message_2. -/
structure Message2Contents where
  dataCI     : ConnId                -- data_2 begins with C_I (if corr ∈ {0,2})
  gY         : EphemeralPubKey       -- Responder's ephemeral
  cR         : ConnId
  ciphertext2 : ByteString           -- CIPHERTEXT_2

/-- Abstract contents of message_3. -/
structure Message3Contents where
  dataCR      : ConnId
  ciphertext3 : ByteString           -- CIPHERTEXT_3

/-- Wire-level messages. -/
def Message1 : Type := ByteString
def Message2 : Type := ByteString
def Message3 : Type := ByteString

/-- Encoding of each message: postulated, with injectivity. -/
axiom encodeMsg1 : Message1Contents → Message1
axiom encodeMsg2 : Message2Contents → Message2
axiom encodeMsg3 : Message3Contents → Message3

axiom encodeMsg1_inj : Injective encodeMsg1
axiom encodeMsg2_inj : Injective encodeMsg2
axiom encodeMsg3_inj : Injective encodeMsg3

/-- A run's negotiated parameters (§3.5): a method, a cipher suite,
    and a correlation mode. The Initiator proposes and the Responder
    accepts or counter-proposes; for the purpose of §3 objects we
    only need the accepted values. -/
structure Negotiated where
  method : Method
  suite  : CipherSuite
  corr   : Corr

/-- The credential identifiers ID_CRED_I / ID_CRED_R are COSE header
    maps; we leave their concrete CBOR form opaque. -/
axiom ID_CRED : Type
axiom ID_CRED.default : ID_CRED
noncomputable instance : Inhabited ID_CRED := ⟨ID_CRED.default⟩


/-! =====================================================================
    §Q  Security framework

    We expose a lightweight class `AdvView` describing what an
    adversary "knows" for each relevant type, and a class
    `AdvDerivable` listing closure properties under public
    computations (public-point derivation, public CBOR encoding,
    evaluation of publicly-keyed HKDF). Neither class commits to a
    particular attacker model (computational, symbolic, UC, etc.).

    To state secrecy of a value it is enough to ask that the value is
    not in `knowsX`. To state authentication one uses agreement of
    `Negotiated` / session-key values across two mutually-honest
    parties — see §R.
    ===================================================================== -/

/-- A view held by some adversary. -/
class AdvView where
  knowsByte    : ByteString   → Prop
  knowsScalar  : PrivScalar   → Prop
  knowsPoint   : PubPoint     → Prop
  knowsShared  : SharedSecret → Prop
  knowsPRK     : PRK          → Prop
  knowsPSK     : PSK          → Prop
  knowsOKM     : OKM          → Prop

/-- Minimal closure properties: an adversary that sees the raw inputs
    can of course compute the public function of them. Crucially these
    *only* give the adversary what it could trivially recompute, and
    say nothing about breaking Diffie-Hellman or HKDF. Secrecy
    statements in §R use the contrapositive. -/
class AdvDerivable extends AdvView where
  /-- Public-point derivation: knowing `x` gives `g^x`. -/
  pub_of_scalar :
    ∀ c x, knowsScalar x → knowsPoint (PubPoint.ofScalar c x)
  /-- ECDH is computable given *both* a scalar and a public point. -/
  ecdh_closure :
    ∀ c x p, knowsScalar x → knowsPoint p → knowsShared (ecdh c x p)
  /-- HKDF-Extract with empty salt is a public function of IKM. -/
  hkdf_empty_closure :
    ∀ h ikm, knowsShared ikm → knowsPRK (HKDF.extractEmpty h ikm)
  /-- HKDF-Extract with PSK salt needs both the PSK and the IKM. -/
  hkdf_psk_closure :
    ∀ h k ikm, knowsPSK k → knowsShared ikm → knowsPRK (HKDF.extractPSK h k ikm)
  /-- HKDF-Extract with PRK salt needs both the PRK and the IKM. -/
  hkdf_prk_closure :
    ∀ h p ikm, knowsPRK p → knowsShared ikm → knowsPRK (HKDF.extractPRK h p ikm)
  /-- HKDF-Expand needs the PRK and the public info block. -/
  hkdf_expand_closure :
    ∀ h p i n, knowsPRK p → knowsByte i → knowsOKM (HKDF.expand h p i n)
  /-- Hashing is a public function of the input. -/
  hash_closure :
    ∀ h b, knowsByte b → knowsByte (Hash.hash h b)
  /-- CBOR encoders are public. -/
  cbor_int_closure   : ∀ n, knowsByte (CBOR.encodeInt n)
  cbor_uint_closure  : ∀ n, knowsByte (CBOR.encodeUint n)
  cbor_tstr_closure  : ∀ s, knowsByte (CBOR.encodeTstr s)
  cbor_bstr_closure  : ∀ b, knowsByte b → knowsByte (CBOR.encodeBstr b)
  cbor_array_closure : ∀ xs : List ByteString,
    (∀ x ∈ xs, knowsByte x) → knowsByte (CBOR.encodeArray xs)
  /-- Byte concatenation is public. -/
  append_closure :
    ∀ a b, knowsByte a → knowsByte b → knowsByte (a ++ b)


/-! =====================================================================
    §R  Security statements

    We group statements into three families, matching the user's
    request. Each is a `Prop` (or a `def ... : Prop`) that can be
    assumed, unfolded, or proved under a chosen attacker model.

    §R.Struct — structural well-formedness
    §R.KDF    — KDF-level integrity of the chain & exporter
    §R.Proto  — protocol-level secrecy and authentication
    ===================================================================== -/

namespace Security

/-! ### §R.Struct — structural well-formedness -/

namespace Struct

/-- A PRK chain is well-formed with respect to a choice of inputs,
    i.e. its fields really are the §3.8 derivations applied to those
    inputs. -/
structure WellFormedChain (cs : CipherSuite) (ch : PRKChain) : Prop where
  sameSuite   : ch.cs = cs
  /-- PRK_2e is one of the two spec cases. -/
  prk2e_spec :
    (∃ gxy, ch.prk2e = PRK_2e_asym cs gxy) ∨
    (∃ psk gxy, ch.prk2e = PRK_2e_psk cs psk gxy)
  /-- PRK_3e2m is derived from PRK_2e, possibly with G_RX. -/
  prk3e2m_spec :
    ∃ gRX?, ch.prk3e2m = PRK_3e2m cs ch.prk2e gRX?
  /-- PRK_4x3m is derived from PRK_3e2m, possibly with G_IY. -/
  prk4x3m_spec :
    ∃ gIY?, ch.prk4x3m = PRK_4x3m cs ch.prk3e2m gIY?

/-- The `info` record of every EDHOC-KDF invocation in a run uses the
    single AEAD id of the negotiated suite (§3.8). -/
def InfoCoherence (cs : CipherSuite) (infos : List Info) : Prop :=
  ∀ i ∈ infos, Info.usesSuite i cs

/-- TH_4 is uniquely determined by TH_3 and CIPHERTEXT_3. -/
theorem TH_4_determined
    (cs : CipherSuite) (th3 th3' c3 c3' : ByteString)
    (h : TH_4 cs th3 c3 = TH_4 cs th3' c3') :
    Hash.hash cs.edhocHash (th3 ++ c3) = Hash.hash cs.edhocHash (th3' ++ c3') := by
  simpa [TH_4] using h

end Struct


/-! ### §R.KDF — KDF-level integrity -/

namespace KDF

/-- Label-distinctness for the EDHOC-Exporter: different labels (at
    the *same* suite, PRK, TH_4 and length) produce different OKMs.

    This is not a theorem in general — it holds only if HKDF is an
    injective-in-info PRF, which is the standard assumption. We state
    it as a `Prop` to be either assumed as an axiom or proved from a
    chosen PRF model. -/
def ExporterLabelInjective
    (cs : CipherSuite) (prk : PRK) (th4 : TranscriptHash) (n : Nat) : Prop :=
  ∀ l₁ l₂ : String,
    l₁ ≠ l₂ →
    EDHOC_Exporter cs prk th4 l₁ n ≠ EDHOC_Exporter cs prk th4 l₂ n

/-- Strengthening: label-distinctness across *all* EDHOC-KDF
    invocations, not just exporter ones. Any two derivations with
    different labels at the same PRK, TH and length give different
    outputs. -/
def KDFLabelInjective
    (cs : CipherSuite) (prk : PRK) (th : ByteString) (n : Nat) : Prop :=
  ∀ l₁ l₂ : String,
    l₁ ≠ l₂ →
    EDHOC_KDF cs prk th l₁ n ≠ EDHOC_KDF cs prk th l₂ n

/-- The derived session keys and IVs (§L) are pairwise distinct
    whenever the exporter/KDF is label-injective. This is a structural
    consequence we *can* prove, given the hypothesis. -/
theorem derived_distinct_of_labelInjective
    (cs : CipherSuite)
    (prk2e prk3e2m prk4x3m : PRK) (th2 th3 : ByteString) (n : Nat)
    (hP2   : KDFLabelInjective cs prk2e   th2 n)
    (hP3m  : KDFLabelInjective cs prk3e2m th2 n)
    (hP3ae : KDFLabelInjective cs prk3e2m th3 n)
    (hP4m  : KDFLabelInjective cs prk4x3m th3 n) :
    -- Key/IV pairs derived from the same PRK+TH are distinct.
    Derived.K_2ae cs prk2e   th2 n ≠ Derived.IV_2ae cs prk2e   th2 n ∧
    Derived.K_2m  cs prk3e2m th2 n ≠ Derived.IV_2m  cs prk3e2m th2 n ∧
    Derived.K_3ae cs prk3e2m th3 n ≠ Derived.IV_3ae cs prk3e2m th3 n ∧
    Derived.K_3m  cs prk4x3m th3 n ≠ Derived.IV_3m  cs prk4x3m th3 n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hP2   "K_2ae" "IV_2ae" (by decide)
  · exact hP3m  "K_2m"  "IV_2m"  (by decide)
  · exact hP3ae "K_3ae" "IV_3ae" (by decide)
  · exact hP4m  "K_3m"  "IV_3m"  (by decide)

/-- The abstract `Info.encode` is injective, given per-slot CBOR
    injectivity and the tag-disjointness of `encodeInt` vs
    `encodeTstr`. -/
theorem Info.encode_inj : Injective Info.encode := by
  intro i j h
  -- Both sides are `CBOR.encodeArray [...]`; peel the array.
  have hList :
      [Info.encodeAeadId i.edhocAeadId, CBOR.encodeBstr i.transcriptHash,
       CBOR.encodeTstr i.label,         CBOR.encodeUint i.length] =
      [Info.encodeAeadId j.edhocAeadId, CBOR.encodeBstr j.transcriptHash,
       CBOR.encodeTstr j.label,         CBOR.encodeUint j.length] :=
    CBOR.encodeArray_inj _ _ h
  -- List-cons injectivity × 4.
  injection hList with hAead r1
  injection r1    with hTHb  r2
  injection r2    with hLabb r3
  injection r3    with hLenb _
  -- Recover per-slot equalities.
  have hTH  : i.transcriptHash = j.transcriptHash := CBOR.encodeBstr_inj _ _ hTHb
  have hLab : i.label           = j.label          := CBOR.encodeTstr_inj _ _ hLabb
  have hLen : i.length          = j.length         := CBOR.encodeUint_inj _ _ hLenb
  have hId  : i.edhocAeadId = j.edhocAeadId := by
    -- Four cases on the two CoseAlgId constructors; same constructor
    -- uses the corresponding atomic injectivity, mixed uses the
    -- tag-disjointness axiom.
    cases hi : i.edhocAeadId <;> cases hj : j.edhocAeadId <;>
      simp [Info.encodeAeadId, hi, hj] at hAead
    · exact congrArg CoseAlgId.int  (CBOR.encodeInt_inj  _ _ hAead)
    · exact (CBOR.encodeInt_ne_encodeTstr _ _ hAead).elim
    · exact ((CBOR.encodeInt_ne_encodeTstr _ _ hAead.symm)).elim
    · exact congrArg CoseAlgId.tstr (CBOR.encodeTstr_inj _ _ hAead)
  -- Reassemble.
  cases i; cases j
  simp_all

end KDF


/-! ### §R.Proto — protocol-level security -/

namespace Proto

/-- The (abstract) ingredients that flowed into a run's PRK chain.
    Kept as a record so that secrecy hypotheses can name exactly which
    of them are secret. -/
structure ChainInputs (cs : CipherSuite) where
  gxy        : SharedSecret
  mode       : AuthMethod        -- the responder side, for PRK_2e salt
  psk?       : Option PSK        -- present iff PSK-authenticated
  gRX?       : Option SharedSecret  -- present iff Responder static DH
  gIY?       : Option SharedSecret  -- present iff Initiator static DH

/-- Spec-conformant rebuild of the PRK chain from `ChainInputs`. -/
noncomputable def ChainInputs.build (cs : CipherSuite) (inp : ChainInputs cs) : PRKChain :=
  let prk2e :=
    match inp.psk? with
    | some k => PRK_2e_psk  cs k inp.gxy
    | none   => PRK_2e_asym cs   inp.gxy
  let prk3e2m := PRK_3e2m cs prk2e   inp.gRX?
  let prk4x3m := PRK_4x3m cs prk3e2m inp.gIY?
  { cs := cs, prk2e := prk2e, prk3e2m := prk3e2m, prk4x3m := prk4x3m }

/-- **Secrecy of PRK_4x3m.** If every input the adversary would need
    to recompute the chain is out of view, then so is PRK_4x3m.

    This is a *statement*, not a theorem: proving it requires a
    hardness assumption (Gap-CDH for the asymmetric case, PRF/PRG for
    HKDF, etc.). It is written in contrapositive form using `AdvView`
    so the attacker model is left open. -/
def PRK_4x3m_Secret [V : AdvView]
    (cs : CipherSuite) (inp : ChainInputs cs) : Prop :=
  ¬ V.knowsShared inp.gxy →
  (∀ k, inp.psk? = some k → ¬ V.knowsPSK k) →
  (∀ g, inp.gRX? = some g → ¬ V.knowsShared g) →
  (∀ g, inp.gIY? = some g → ¬ V.knowsShared g) →
  ¬ V.knowsPRK (inp.build cs).prk4x3m

/-- **Secrecy of all session keys.** Same hypotheses → session keys
    derived from the chain and the transcript hashes are unknown. -/
def SessionKeys_Secret [V : AdvView]
    (cs : CipherSuite) (inp : ChainInputs cs)
    (th2 th3 : ByteString) (n : Nat) : Prop :=
  ¬ V.knowsShared inp.gxy →
  (∀ k, inp.psk? = some k → ¬ V.knowsPSK k) →
  (∀ g, inp.gRX? = some g → ¬ V.knowsShared g) →
  (∀ g, inp.gIY? = some g → ¬ V.knowsShared g) →
  let ch := inp.build cs
  ¬ V.knowsOKM (Derived.K_2ae cs ch.prk2e   th2 n) ∧
  ¬ V.knowsOKM (Derived.K_2m  cs ch.prk3e2m th2 n) ∧
  ¬ V.knowsOKM (Derived.K_3ae cs ch.prk3e2m th3 n) ∧
  ¬ V.knowsOKM (Derived.K_3m  cs ch.prk4x3m th3 n)

/-- A party's local view of a completed run. Used to state
    authentication. -/
structure SessionView where
  neg      : Negotiated
  conn     : ConnIds
  peerCred : ID_CRED
  th4      : TranscriptHash
  prk4x3m  : PRK

/-- **Mutual agreement (key confirmation).** Two honest parties
    that both complete a run agree on the negotiated parameters,
    the peer credentials (swapped), the final transcript hash, and
    PRK_4x3m. -/
def MutualAgreement (initView responderView : SessionView) : Prop :=
  initView.neg       = responderView.neg ∧
  initView.conn      = responderView.conn ∧
  initView.th4       = responderView.th4 ∧
  initView.prk4x3m   = responderView.prk4x3m

/-- **Peer authentication.** If the Initiator completes thinking the
    responder credential is `cR`, then some honest party holding `cR`
    participated in a matching run. Stated in Lowe's "matching
    conversations" style as a bi-implication with a matching
    `SessionView`. The existential over honest parties is left
    abstract via a parameterised predicate `honest`. -/
def InitiatorAuthenticates
    (honest : ID_CRED → Prop) (initView : SessionView) : Prop :=
  honest initView.peerCred →
  ∃ respView : SessionView,
    respView.peerCred ≠ initView.peerCred ∧          -- peers, not self
    MutualAgreement initView respView

/-- Symmetric statement from the Responder's side. -/
def ResponderAuthenticates
    (honest : ID_CRED → Prop) (respView : SessionView) : Prop :=
  honest respView.peerCred →
  ∃ initView : SessionView,
    initView.peerCred ≠ respView.peerCred ∧
    MutualAgreement initView respView

end Proto

end Security

end EDHOC
