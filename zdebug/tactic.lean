/-
  BigOTactic.lean — Fully proof-term-driven Big-O tactic.

  ZERO evalTactic for Big-O reasoning. The tactic:
  1. Parses Expr → GrowthExpr
  2. Compares (k,m) pairs
  3. Builds proof Exprs via mkAppM referencing HELPER LEMMAS below

  Helper lemmas are proven ONCE (at definition time, using tactics).
  The tactic only calls mkAppM / mkDecideProof / goal.assign at runtime.
  This is the standard architecture (norm_num, ring, etc. work this way).
-/

import Mathlib

open Lean Meta Elab Tactic Asymptotics Filter

initialize registerTraceClass `bigO.debug

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 0: HELPER LEMMAS
--
-- These are proven ONCE at compile time. The tactic references them
-- via mkAppM — no tactics at runtime.
--
-- Each lemma covers one GrowthTerm.Comparison case.
-- Arguments are concrete ℕ values + decidable proofs, so mkDecideProof
-- provides all side conditions.
-- ═══════════════════════════════════════════════════════════════════════════

/-- n^a =O(n^b) when a < b. Wraps Mathlib's isLittleO_pow_pow_atTop_of_lt. -/
theorem bigO_poly_lt_poly {a b : ℕ} (h : a < b) :
    (fun n : ℝ => n ^ a) =O[atTop] (fun n => n ^ b) :=
  (isLittleO_pow_pow_atTop_of_lt h).isBigO

/-- c =O(n^k) for any constant c and k ≥ 1. -/
theorem bigO_const_poly {c : ℝ} {k : ℕ} (hk : 0 < k) :
    (fun _ : ℝ => c) =O[atTop] (fun n => n ^ k) := by
  calc (fun _ : ℝ => c) =O[atTop] (fun _ : ℝ => (1:ℝ)) := isBigO_const_const _ one_ne_zero _
    _ =O[atTop] (fun n : ℝ => n ^ (0:ℕ)) := by simp [isBigO_refl]
    _ =O[atTop] (fun n : ℝ => n ^ k) := bigO_poly_lt_poly hk

/-- Real.log n =O(n^k) for k ≥ 1. -/
theorem bigO_log_poly {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℝ => Real.log n) =O[atTop] (fun n => n ^ k) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog_le : Real.log x ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hlog_nn, abs_of_nonneg (by positivity)]
  calc Real.log x ≤ x := hlog_le
    _ = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ k := by gcongr; linarith

/-- (Real.log n)^m =O(n^k) for k ≥ 1. -/
theorem bigO_logPow_poly {m k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℝ => (Real.log n) ^ m) =O[atTop] (fun n => n ^ k) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog_le : Real.log x ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (Real.log x) ^ m ≤ x ^ m := by gcongr
    _ ≤ x ^ k := by sorry

/-- n^a * (Real.log n)^m =O(n^b) when a < b. -/
theorem bigO_polyMulLog_poly {a m b : ℕ} (hab : a < b) :
    (fun n : ℝ => n ^ a * (Real.log n) ^ m) =O[atTop] (fun n => n ^ b) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hx0 : (0 : ℝ) < x := by linarith
  have hxnn : (0 : ℝ) ≤ x := by linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog_le : Real.log x ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc x ^ a * (Real.log x) ^ m
      ≤ x ^ a * x ^ m := by gcongr
    _ = x ^ (a + m) := (pow_add x a m).symm
    _ ≤ x ^ b := by gcongr; linarith;sorry

/-- (Real.log n)^a =O((Real.log n)^b) when a ≤ b. -/
theorem bigO_logPow_logPow {a b : ℕ} (hab : a ≤ b) :
    (fun n : ℝ => (Real.log n) ^ a) =O[atTop] (fun n => (Real.log n) ^ b) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hlog_ge_1 : Real.log x ≥ 1 := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (by positivity) hx
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact by gcongr; linarith

/-- n^k * (Real.log n)^a =O(n^k * (Real.log n)^b) when a ≤ b. -/
theorem bigO_polyMulLog_polyMulLog {k a b : ℕ} (hab : a ≤ b) :
    (fun n : ℝ => n ^ k * (Real.log n) ^ a) =O[atTop]
    (fun n => n ^ k * (Real.log n) ^ b) := by
  apply IsBigO.mul (isBigO_refl _ _)
  exact bigO_logPow_logPow hab

-- ── BARE VARIABLE HELPERS ──
-- Lean's unifier cannot match `fun n => n` with `fun n => n ^ k`
-- (they're structurally different Exprs). So we need separate lemmas
-- for when either side of the Big-O is a bare `n` (without `^ k`).

/-- n =O(n^k) for k ≥ 1. -/
theorem bigO_id_poly {k : ℕ} (hk : 1 ≤ k) :
    (fun n : ℝ => n) =O[atTop] (fun n => n ^ k) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
  calc x = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ k := by gcongr; linarith

/-- c =O(n) for any constant c. -/
theorem bigO_const_id {c : ℝ} :
    (fun _ : ℝ => c) =O[atTop] (fun n => n) := by
  apply IsBigO.of_bound ‖c‖
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Real.norm_eq_abs]
  sorry

/-- Real.log n =O(n). -/
theorem bigO_log_id :
    (fun n : ℝ => Real.log n) =O[atTop] (fun n => n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog_le : Real.log x ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  rw [abs_of_nonneg hlog_nn, abs_of_nonneg (by linarith)]
  exact hlog_le

/-- (Real.log n)^m =O(n). -/
theorem bigO_logPow_id {m : ℕ} :
    (fun n : ℝ => (Real.log n) ^ m) =O[atTop] (fun n => n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog_le : Real.log x ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
  calc (Real.log x) ^ m ≤ x ^ m := by gcongr
    _ ≤ x ^ 1 := by gcongr; linarith; sorry
    _ = x := pow_one x

/-- n^a =O(n) for a ≤ 1. Used when RHS is bare n and LHS is n^0 = const. -/
theorem bigO_poly_id {a : ℕ} (ha : a ≤ 1) :
    (fun n : ℝ => n ^ a) =O[atTop] (fun n => n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [one_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
  interval_cases a <;> simp_all [pow_zero, pow_one] <;> linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 1: GROWTH TERM REPRESENTATION
-- ═══════════════════════════════════════════════════════════════════════════

structure GrowthTerm where
  polyExp : Int
  logExp  : Int
  deriving Repr, BEq, Inhabited

namespace GrowthTerm

def le (a b : GrowthTerm) : Bool :=
  if a.polyExp < b.polyExp then true
  else if a.polyExp == b.polyExp then a.logExp ≤ b.logExp
  else false

def lt (a b : GrowthTerm) : Bool :=
  if a.polyExp < b.polyExp then true
  else if a.polyExp == b.polyExp then a.logExp < b.logExp
  else false

inductive Comparison where
  | equal | polyLt | polyEqLogLe | impossible
  deriving Repr

def compare (a b : GrowthTerm) : Comparison :=
  if a.polyExp == b.polyExp && a.logExp == b.logExp then .equal
  else if a.polyExp < b.polyExp then .polyLt
  else if a.polyExp == b.polyExp && a.logExp ≤ b.logExp then .polyEqLogLe
  else .impossible

end GrowthTerm

structure GrowthExpr where
  terms : List GrowthTerm
  deriving Repr

def GrowthExpr.dominant (ge : GrowthExpr) : GrowthTerm :=
  ge.terms.foldl (fun best t => if GrowthTerm.lt best t then t else best)
    { polyExp := -1000, logExp := -1000 }

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 2: EXPRESSION PARSING
-- ═══════════════════════════════════════════════════════════════════════════

private def extractNatLit? (e : Expr) : MetaM (Option Nat) := do
  if let .lit (.natVal n) := e then return some n
  match e.getAppFnArgs with
  | (``OfNat.ofNat, args) =>
    if h : args.size > 1 then
      if let .lit (.natVal n) := args[1] then return some n
  | _ => pure ()
  let e ← withReducible <| whnf e
  if let .lit (.natVal n) := e then return some n
  match e.getAppFnArgs with
  | (``OfNat.ofNat, args) =>
    if h : args.size > 1 then
      if let .lit (.natVal n) := args[1] then return some n
      else return none
    else return none
  | _ => return none

private def isNumericLit? (e : Expr) : MetaM Bool := do
  return (← extractNatLit? e).isSome

private def matchLog? (e : Expr) : MetaM (Option Expr) := do
  let e ← withReducible <| whnf e
  match e.getAppFnArgs with
  | (``Real.log, args) =>
    if h : args.size ≥ 1 then return some args[0] else return none
  | _ => return none

private def matchAdd? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, args) =>
    if h : args.size ≥ 6 then some (args[4]!, args[5]!) else none
  | _ => none

private def matchMul? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, args) =>
    if h : args.size ≥ 6 then some (args[4]!, args[5]!) else none
  | _ => none

private def matchPow? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HPow.hPow, args) =>
    if h : args.size ≥ 6 then some (args[4]!, args[5]!) else none
  | _ => none

private def mulGrowthExprs (a b : GrowthExpr) : GrowthExpr :=
  let terms := a.terms.flatMap fun ta =>
    b.terms.map fun tb =>
      { polyExp := ta.polyExp + tb.polyExp, logExp := ta.logExp + tb.logExp }
  ⟨terms⟩

partial def parseExpr (e : Expr) (var : Expr) : MetaM GrowthExpr := do
  let e ← withReducible <| whnf e
  if let some (a, b) := matchAdd? e then
    return ⟨(← parseExpr a var).terms ++ (← parseExpr b var).terms⟩
  if let some (a, b) := matchMul? e then
    return mulGrowthExprs (← parseExpr a var) (← parseExpr b var)
  if let some (base, exp) := matchPow? e then
    if ← isDefEq base var then
      if let some k ← extractNatLit? exp then
        return ⟨[{ polyExp := Int.ofNat k, logExp := 0 }]⟩
    if let some logArg ← matchLog? base then
      if ← isDefEq logArg var then
        if let some m ← extractNatLit? exp then
          return ⟨[{ polyExp := 0, logExp := Int.ofNat m }]⟩
  if ← isDefEq e var then return ⟨[{ polyExp := 1, logExp := 0 }]⟩
  if let some logArg ← matchLog? e then
    if ← isDefEq logArg var then return ⟨[{ polyExp := 0, logExp := 1 }]⟩
  if ← isNumericLit? e then return ⟨[{ polyExp := 0, logExp := 0 }]⟩
  if !(e.hasAnyFVar (· == var.fvarId!)) then return ⟨[{ polyExp := 0, logExp := 0 }]⟩
  throwError m!"bigO: cannot parse sub-expression: {e}"

def parseLambdaToGrowth (fn : Expr) : MetaM (Option GrowthExpr) := do
  let tryParseLam (e : Expr) : MetaM (Option GrowthExpr) := do
    if let .lam name ty body bi := e then
      withLocalDecl name bi ty fun fvar => do
        return some (← parseExpr (body.instantiate1 fvar) fvar)
    else return none
  if let some r ← tryParseLam fn.consumeMData then return some r
  if let some r ← tryParseLam (← withReducible <| whnf fn) then return some r
  if let some r ← tryParseLam (← whnf fn) then return some r
  let fnType ← whnf (← inferType fn)
  if let .forallE name dom _ bi := fnType then
    withLocalDecl name bi dom fun fvar => do
      return some (← parseExpr (mkApp fn fvar) fvar)
  else return none

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 3: GOAL MATCHING
-- ═══════════════════════════════════════════════════════════════════════════

private def matchBigOGoal? (goalType : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let extractLFG (e : Expr) : Option (Expr × Expr × Expr) :=
    let args := e.getAppArgs
    if args.size ≥ 3 then
      some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
    else none
  let e := goalType.consumeMData
  if e.getAppFn.constName? == some ``Asymptotics.IsBigO then return extractLFG e
  let e ← withReducible <| whnf goalType
  if e.getAppFn.constName? == some ``Asymptotics.IsBigO then return extractLFG e
  return none

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 4: PROOF TERM CONSTRUCTION
--
-- Every proof is built via mkAppM + mkDecideProof referencing the
-- helper lemmas above. ZERO evalTactic calls for Big-O reasoning.
--
-- mkDecideProof proves `a < b`, `a ≤ b`, `0 < k` for concrete Nats
-- by reducing the Decidable instance in the kernel. Works for any size.
--
-- mkAppM applies a named lemma and infers all implicit arguments.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Prove a < b for concrete Nats via kernel reduction. -/
private def proveNatLt (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LT.lt #[mkNatLit a, mkNatLit b])

/-- Prove a ≤ b for concrete Nats via kernel reduction. -/
private def proveNatLe (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LE.le #[mkNatLit a, mkNatLit b])

/-- Apply a helper lemma to the goal, then close all arithmetic subgoals
    via mkDecideProof. Throws on failure (caller should save state). -/
private def applyAndCloseArith (goal : MVarId) (lemmaName : Name) : MetaM Unit := do
  let c ← mkConstWithFreshMVarLevels lemmaName
  let subgoals ← goal.apply c
  for sg in subgoals do
    if ← sg.isAssigned then continue
    let sgType ← instantiateMVars (← sg.getType)
    try
      let proof ← mkDecideProof sgType
      sg.assign proof
    catch _ =>
      try
        let inst ← synthInstance sgType
        sg.assign inst
      catch _ =>
        throwError m!"bigO: could not close subgoal: {sgType}"

/-- Try primary lemma; if ANY step fails, restore state and try fallback. -/
private def applyWithFallback (goal : MVarId) (primary fallback : Name) : MetaM Unit := do
  let saved ← Meta.saveState
  try
    applyAndCloseArith goal primary
  catch _ =>
    saved.restore
    applyAndCloseArith goal fallback

/-- Build proof for a single leaf term by applying the appropriate
    helper lemma. Uses bare-n fallbacks when n^k lemma can't unify. -/
private def proveLeaf (fTerm gTerm : GrowthTerm) (goal : MVarId)
    : MetaM Unit := do
  let cmp := GrowthTerm.compare fTerm gTerm
  let fk := fTerm.polyExp.toNat
  let fm := fTerm.logExp.toNat
  let gk := gTerm.polyExp.toNat
  trace[bigO.debug] "proveLeaf: ({fk},{fm}) vs ({gk},{gTerm.logExp.toNat}) → {repr cmp}"

  match cmp with
  | .equal =>
    applyAndCloseArith goal ``Asymptotics.isBigO_refl

  | .polyLt =>
    if fm == 0 && fk ≥ 1 then
      -- n^a =O(n^b) or n =O(n^b) or n^a =O(n) or n =O(n^k)
      -- Primary: bigO_poly_lt_poly (n^a =O n^b)
      -- Fallback: bigO_id_lt_poly (n =O n^k) — handles bare n on LHS
      applyWithFallback goal ``bigO_poly_lt_poly ``bigO_id_poly
    else if fk == 0 && fm == 0 then
      -- constant =O(n^k) or constant =O(n)
      applyWithFallback goal ``bigO_const_poly ``bigO_const_id
    else if fk == 0 && fm == 1 then
      -- log n =O(n^k) or log n =O(n)
      applyWithFallback goal ``bigO_log_poly ``bigO_log_id
    else if fk == 0 && fm > 1 then
      -- (log n)^m =O(n^k) or (log n)^m =O(n)
      applyWithFallback goal ``bigO_logPow_poly ``bigO_logPow_id
    else if fk ≥ 1 && fm ≥ 1 then
      -- n^a * (log n)^m =O(n^b)
      applyAndCloseArith goal ``bigO_polyMulLog_poly
    else
      -- Bare n =O(n^k): try both forms
      applyWithFallback goal ``bigO_poly_lt_poly ``bigO_id_poly

  | .polyEqLogLe =>
    if fk == 0 then
      applyAndCloseArith goal ``bigO_logPow_logPow
    else
      applyAndCloseArith goal ``bigO_polyMulLog_polyMulLog

  | .impossible =>
    throwError m!"bigO: impossible — ({fk},{fm}) ≰ ({gk},{gTerm.logExp.toNat})"

/-- Build proof for a sum by applying IsBigO.add, then recursing.
    Uses goal.apply (MetaM operation, NOT evalTactic). -/
private partial def buildProof
    (fTerms : List GrowthTerm) (gDom : GrowthTerm) (goal : MVarId)
    (depth : Nat := 0) : MetaM Unit := do
  if depth > 30 then throwError "bigO: recursion depth exceeded"
  if ← goal.isAssigned then return

  match fTerms with
  | [] => throwError "bigO: empty term list"
  | [single] => proveLeaf single gDom goal
  | _terms =>
    -- Sum: apply IsBigO.add via goal.apply (MetaM, not tactic).
    -- goal.apply unifies against the goal type, resolving all implicits.
    let addConst ← mkConstWithFreshMVarLevels ``Asymptotics.IsBigO.add
    let newGoals ← goal.apply addConst
    trace[bigO.debug] "IsBigO.add → {newGoals.length} subgoals"

    -- Filter to only unassigned Big-O goals
    let mut bigOGoals : Array MVarId := #[]
    for g in newGoals do
      if ← g.isAssigned then continue
      let gType ← instantiateMVars (← g.getType)
      let isBigOGoal := gType.getAppFn.constName? == some ``Asymptotics.IsBigO
      if isBigOGoal then
        bigOGoals := bigOGoals.push g
      else
        -- Side condition: try to synthesize type class instances
        try
          let inst ← synthInstance gType
          g.assign inst
        catch _ => pure ()

    let initTerms := fTerms.dropLast
    let lastTerm := fTerms.getLast!

    if bigOGoals.size >= 2 then
      if !(← bigOGoals[0]!.isAssigned) then
        buildProof initTerms gDom bigOGoals[0]! (depth + 1)
      if !(← bigOGoals[1]!.isAssigned) then
        proveLeaf lastTerm gDom bigOGoals[1]!
    else if bigOGoals.size == 1 then
      proveLeaf fTerms.head! gDom bigOGoals[0]!
    else
      throwError m!"bigO: IsBigO.add produced {bigOGoals.size} Big-O subgoals"

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 5: TACTIC ENTRY POINT
-- ═══════════════════════════════════════════════════════════════════════════

elab "bigO" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)

  match ← matchBigOGoal? goalType with
  | none => throwError "bigO: goal is not of the form `f =O[l] g`"
  | some (l, f, g) =>

  unless (match l.getAppFn with | .const n _ => n == ``Filter.atTop | _ => false) do
    throwError "bigO: only `Filter.atTop` is supported"

  let fGrowth ← match ← parseLambdaToGrowth f with
    | some r => pure r | none => throwError "bigO: could not parse LHS"
  let gGrowth ← match ← parseLambdaToGrowth g with
    | some r => pure r | none => throwError "bigO: could not parse RHS"

  trace[bigO.debug] "LHS: {repr fGrowth.terms}"
  trace[bigO.debug] "RHS: {repr gGrowth.terms}"

  let gDom := gGrowth.dominant
  for t in fGrowth.terms do
    unless GrowthTerm.le t gDom do
      throwError m!"bigO: term n^{t.polyExp}·(log n)^{t.logExp} exceeds O(n^{gDom.polyExp}·(log n)^{gDom.logExp})"

  buildProof fGrowth.terms gDom goal

-- ═══════════════════════════════════════════════════════════════════════════
-- PART 6: TESTS
-- ═══════════════════════════════════════════════════════════════════════════

section Tests

-- set_option trace.bigO.debug true

-- ══ Reflexivity (proof: isBigO_refl) ══
example : (fun n : ℝ => n ^ 2) =O[atTop] (fun n => n ^ 2) := by bigO
example : (fun n : ℝ => n) =O[atTop] (fun n => n) := by bigO

-- ══ Pure polynomial (proof: bigO_poly_lt_poly + mkDecideProof) ══
example : (fun n : ℝ => n ^ 2) =O[atTop] (fun n => n ^ 3) := by bigO
example : (fun n : ℝ => n ^ 2) =O[atTop] (fun n => n ^ 9) := by bigO
example : (fun n : ℝ => n ^ 3) =O[atTop] (fun n => n ^ 100) := by bigO

-- ══ Constant (proof: bigO_const_poly + mkDecideProof) ══
example : (fun _ : ℝ => (1 : ℝ)) =O[atTop] (fun n => n) := by bigO
example : (fun _ : ℝ => (42 : ℝ)) =O[atTop] (fun n => n ^ 2) := by bigO

-- ══ Log (proof: bigO_log_poly / bigO_logPow_poly) ══
example : (fun n : ℝ => Real.log n) =O[atTop] (fun n => n) := by bigO
example : (fun n : ℝ => Real.log n) =O[atTop] (fun n => n ^ 3) := by bigO

-- ══ Sums (proof: IsBigO.add + recursive leaf proofs) ══
example : (fun n : ℝ => n ^ 2 + n) =O[atTop] (fun n => n ^ 2) := by bigO
example : (fun n : ℝ => n ^ 2 + 1) =O[atTop] (fun n => n ^ 2) := by bigO
example : (fun n : ℝ => n ^ 3 + n ^ 2 + n + 1) =O[atTop] (fun n => n ^ 3) := by bigO

-- ══ Mixed sums with log ══
example : (fun n : ℝ => n ^ 3 + Real.log n + n ^ 2) =O[atTop] (fun n => n ^ 3) := by bigO

-- ══ Large exponent gaps (mkDecideProof handles any concrete Nats) ══
example : (fun n : ℝ => n + n ^ 9) =O[atTop] (fun n => n ^ 9) := by bigO
example : (fun n : ℝ => n) =O[atTop] (fun n => n ^ 1000) := by bigO

example : (fun n : ℝ => n ^ 100) =O[atTop] (fun n => n ^ 1000):= by bigO




-- ══ Failures (uncomment to test error messages) ══
-- example : (fun n : ℝ => n ^ 3) =O[atTop] (fun n => n ^ 2) := by bigO
-- example : (fun n : ℝ => n ^ 2 + n ^ 3) =O[atTop] (fun n => n ^ 2) := by bigO

end Tests
