/-
Copyright (c) 2026.  Released under the Apache 2.0 license as described in the file LICENSE.
-/
import EDHOC.Trace

/-!
# Tamarin: multiset rewrite framework (§3.3)

A Tamarin specification is a collection of *multiset rewrite rules*

  `l --[e]→ r`

where `l`, `r` are multisets of facts and `e` is a multiset of action
labels.  Section 3.3 only needs us to talk about rules and facts at the
syntactic level — the semantics is delegated to Tamarin itself — so we
just provide:

* `Fact` — an open enumeration of the fact symbols Section 3 mentions;
* `Rule` — a record `{ name; lhs; actions; rhs }` whose fields are the
  three multisets and a human-readable identifier.

The action labels `e` reuse `EDHOC.Action` from `EDHOC.Trace`.
-/

namespace EDHOC.Tamarin

/-- Tamarin fact symbols.  Section 3 mentions a small finite set; new
    rules can introduce additional persistent state via `State name args`. -/
inductive Fact
  /-- `Fr(t)` — freshness. -/
  | Fr   (t : Term)
  /-- `In(t)` — message arriving on the network. -/
  | In   (t : Term)
  /-- `Out(t)` — message sent on the network. -/
  | Out  (t : Term)
  /-- `!KU(t)` — adversary knowledge fact (Tamarin built-in). -/
  | KU   (t : Term)
  /-- `!LTK_SIG(A, k)` — `A`'s SIG long-term key. -/
  | LTK_SIG  (A : Party) (k : Key)
  /-- `!LTK_STAT(A, k)` — `A`'s STAT long-term key. -/
  | LTK_STAT (A : Party) (k : Key)
  /-- `!PK_SIG(A, p)` — `A`'s SIG public key. -/
  | PK_SIG   (A : Party) (p : Term)
  /-- `!PK_STAT(A, p)` — `A`'s STAT public key. -/
  | PK_STAT  (A : Party) (p : Term)
  /-- A persistent state fact carrying inter-rule data
      (`StI` / `StR` of §3.4.3). -/
  | State    (name : String) (args : List Term)

/-- A Tamarin multiset rewrite rule `lhs --[actions]→ rhs`. -/
structure Rule where
  /-- Human-readable rule name, matching the paper. -/
  name    : String
  /-- Left-hand side multiset of facts. -/
  lhs     : List Fact
  /-- Action labels emitted on rule application. -/
  actions : List Action
  /-- Right-hand side multiset of facts. -/
  rhs     : List Fact

end EDHOC.Tamarin
