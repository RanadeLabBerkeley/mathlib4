# EDHOC: a Lean 4 formalisation

A Lean 4 transcription of Section 3 of

> Karl Norrman, Vaishnavi Sundararajan, Alessandro Bruni,
> *"Formal Analysis of EDHOC Key Establishment for Constrained IoT Devices"*,
> arXiv:2007.11427v3 (Jul 2021),

together with the Tamarin-verified Table 1 (posited as `axiom Table1`)
and a single bundled headline result `EDHOC_main` that pulls every
verified and inferred property into one statement.

The library has **no Mathlib dependency** — it is its own `lean_lib EDHOC`
in `lakefile.lean` and builds in seconds.

```bash
lake build EDHOC
```

## What's where

The files are arranged so each concept sits on its own page (≤ ~170 lines).

| File                            | Topic                                                 | Paper §       |
| ------------------------------- | ----------------------------------------------------- | ------------- |
| `Preliminaries.lean`            | Term algebra, parties, timestamps                     | §3.1, §3.2    |
| `Trace.lean`                    | `Action`, `Trace`, `sameKind` axiom                   | §3.2          |
| `Events.lean`                   | `K`, `ALTK`, `AEph`, `IS / IC / RS / RC`, `sk_term`   | §3.2          |
| `Properties.lean`               | `PFS`, `InjAgreeI/R`, `ImpAgreeI/R`                   | §3.2.1–§3.2.2 |
| `AgreedParameters.lean`         | `Role`, `SP`, `SF`                                    | §3.2.3        |
| `Inferred.lean`                 | I-side `KCIResistant` / `UKSResistant` / `EntityAuth` | §3.2.4        |
| `Tamarin/Framework.lean`        | `Fact`, `Rule`                                        | §3.3          |
| `Tamarin/Primitives.lean`       | AEAD, sign, hash, DH, XOR (`Prim` namespace)          | §3.4.1        |
| `Tamarin/Environment.lean`      | `registerLTK_*`, `LTKRev`, `EphKeyRev`                | §3.4.2        |
| `Tamarin/Roles.lean`            | `R2_STAT_SIG`                                         | §3.4.3        |
| `Tamarin/Properties.lean`       | Encoding of `secrecyPFS`, both directions             | §3.5          |
| `Table1.lean`                   | `Method`, `axiom Table1`, I-side corollaries          | §5 / Table 1  |
| `Secrecy.lean`                  | `honest_world_secrecy` (and localised version)        | (corollary)   |
| `Dual.lean`                     | R-side duals + the combined `UKSFull`                 | (corollary)   |
| `MainTheorem.lean`              | The headline bundle: `EDHOC_main`, `EDHOC_safe_world` | §3 summary    |

## Where to start reading

If you only want to know what the library *delivers*, read in this order:

1. `MainTheorem.lean` — the bundle `EDHOC_main_security` and the slogan
   form `EDHOC_safe_world`.
2. `Table1.lean` — what Tamarin actually verified (`axiom Table1`).
3. `Properties.lean` — what each of those verified properties means.

If you want to understand the **model** that the properties are stated
over:

1. `Preliminaries.lean` → `Trace.lean` → `Events.lean`.
2. `AgreedParameters.lean` for the `S_P` / `S_F` records.

If you want to see how the protocol is **encoded for Tamarin**:

1. `Tamarin/Framework.lean` — what a Tamarin rule looks like.
2. `Tamarin/Primitives.lean` and `Tamarin/Environment.lean` — function
   symbols and ambient rules.
3. `Tamarin/Roles.lean` — one fully-transcribed protocol rule.
4. `Tamarin/Properties.lean` — how the high-level `PFS` of
   `Properties.lean` is encoded as Tamarin's `secrecyPFS`.

## The headline result

```lean
theorem EDHOC_main
    (m : Method) (τ : Trace) (h : honestRun m τ) :
    EDHOC_main_security τ
```

unconditionally bundles all five rows of Table 1 plus KCI resistance on
both sides; under each property's natural honesty hypothesis it also
gives mutual entity authentication, UKS resistance on both sides, the
combined `UKSFull`, and honest-world secrecy.

The "no leaks ever happen" specialisation:

```lean
theorem EDHOC_safe_world
    (m : Method) (τ : Trace) (h : honestRun m τ)
    (noLTK : ∀ t A, ¬ ALTK τ t A)
    (noEph : ∀ t A Z, ¬ AEph τ t A Z) : ...
```

collapses every escape clause and lists the seven Tamarin-verified plus
six inferred properties as a single unconditional conjunction.

## Import DAG

```
Preliminaries
   │
Trace ────────────────► Tamarin/Framework
   │                       │
Events                  Tamarin/Primitives
   │                       │
Properties ──────────► Tamarin/Environment
   │     ╲                 │
   │      AgreedParameters Tamarin/Roles
   │     ╱                 │
Inferred                   Tamarin/Properties (also needs Properties)
   │
Table1
   ├──── Secrecy
   └──── Dual
            │
       MainTheorem
```

## Axioms used

The library is `axiom`-heavy by design — the paper is parametric in the
underlying cryptographic algebra, and Tamarin discharges the verification
externally.  Concretely:

* The term algebra (`Party`, `Term`, `Key`, `Eph`, `Term.pair`,
  `Term.pair_inj`).
* Timestamps (`Time`, `before`, `before_irrefl`, `before_trans`).
* The trace uniqueness axiom `Trace.uniq_per_type`.
* The deduction rule `K_pair_proj`.
* Cryptographic primitives in `Tamarin/Primitives.lean`
  (`aeadEncrypt`, `sign`, `expg`, `XOR`, …) with their defining
  equations.
* The coercions `sk_term`, `Key.toTerm`, `Party.toTerm`, `pk_of`,
  `SP_to_paramSet`, `SF_to_paramSet` and the latter two's injectivity.
* `honestRun` — the abstract "this trace is an execution of method `m`".
* **`Table1`** — the Tamarin-verified five-row table.

Beyond these, *every* result in the library is proved.

## Renaming history

The library used to live in two monolithic files, `paper_section_3.lean`
and `PROOF_section_3.lean`, at the workspace root.  Those have been
replaced by the modular layout above, and the `lean_lib` is registered
via `globs := #[.submodules `EDHOC]` so new files dropped under `EDHOC/`
are picked up automatically.
