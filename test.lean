-- import Mathlib


-- variable {a b c: ℝ}

-- #check (min_le_left a b : min a b ≤ a)
-- #check (min_le_right a b : min a b ≤ b)
-- #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- example : min a b = min b a := by
--   apply le_antisymm
--   · show min a b ≤ min b a
--     apply le_min
--     · apply min_le_right
--     apply min_le_left
--   · show min b a ≤ min a b
--     apply le_min
--     · apply min_le_right
--     apply min_le_left

-- example : max a b = max b a := by
--   apply le_antisymm
--   · show max a b ≤ max b a
--     · apply max_le
--       · apply le_max_right
--       · apply le_max_left
--   · show max b a ≤ max a b
--     apply max_le
--     · apply le_max_right
--     · apply le_max_left

-- example : min (min a b) c = min a (min b c) := by
--   apply le_antisymm
--   · apply le_min
--     · simp
--     · simp
--   · apply le_min
--     · simp
--     · simp

-- theorem aux : min a b + c ≤ min (a + c) (b + c) := by
--   apply le_min
--   · linarith [min_le_left a b]
--   · linarith [min_le_right a b]


-- #check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

-- example : |a| - |b| ≤ |a - b| := by
--   suffices |a| ≤ |a - b| + |b| by
--     linarith
--   suffices |a| ≤ |a - b + b| by
--     calc |a| ≤ |a - b + b| := this
--     _ ≤ |a - b| + |b| := abs_add_le (a - b) (b)
--   conv =>
--     right
--     congr
--     rw [sub_add_cancel]

-- variable {x y z w : ℝ}
-- example (h0 : x ∣ y) (h1 : y ∣  z) : x ∣ z :=
--    dvd_trans h0 h1

-- example : x ∣ y * x * z := by
--   apply dvd_mul_of_dvd_left
--   apply dvd_mul_left
-- example : x ∣ x ^ 2 := by
--   apply dvd_mul_left


-- #check dvd_add
-- example (h : x ∣ w) : x ∣ (y * (x * z) + x ^ 2 + w ^ 2) := by
--   apply dvd_add
--   apply dvd_add
--   apply dvd_mul_of_dvd_right
--   apply dvd_mul_of_dvd_left
--   simp
--   apply dvd_mul_left
--   rw [pow_two]
--   apply dvd_trans h (show w ∣ w * w by apply dvd_mul_left)


-- variable {m n : ℕ}
-- example : Nat.gcd m n = Nat.gcd n m := by
--  apply dvd_antisymm
--  apply Nat.dvd_gcd_iff.2
--  constructor
--  apply Nat.gcd_dvd_right
--  apply Nat.gcd_dvd_left
--  apply Nat.dvd_gcd_iff.2
--  constructor
--  apply Nat.gcd_dvd_right
--  apply Nat.gcd_dvd_left

-- variable {α : Type*} [PartialOrder α]

-- variable (x y z : α)
-- #check x ≤ y
-- #check (le_refl x : x ≤ x)
-- #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- variable {α : Type*} [Lattice α]
-- variable (x y z : α)
-- #check x ⊓ y
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
-- #check x ⊔ y
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)


-- example : x ⊓ y = y ⊓ x := by
-- apply le_antisymm
-- apply le_inf
-- apply inf_le_right
-- apply inf_le_left
-- apply le_inf
-- apply inf_le_right
-- apply inf_le_left


-- -- inductive NatC where
-- --   | zero : NatC
-- --   | succ (n : NatC) : NatC

-- -- open NatC

-- -- def pred (n : NatC) : NatC :=
-- --   match n with
-- --   | zero => zero
-- --   | succ (n : NatC) => n

-- -- #eval pred (NatC.succ (NatC.succ NatC.zero))



-- def IsEvenNat (n: Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ (n: Nat) => not (IsEvenNat n)

-- #eval IsEvenNat (10)


-- -- def div (n : Nat) (k : Nat) : Nat :=
-- --   if n < k then
-- --     0
-- --   else Nat.succ (div (n - k) k)

-- structure PPointC (α : Type) where
--   point ::
--   x : α
--   y : α

-- def NatOrigin : PPointC Nat := {x := 0, y := 0}

-- def replace_f_c (α : Type) (old : PPointC α) (new_x : α) : PPointC α :=
--   {old with x := new_x : (PPointC α)}

-- inductive SignC where
--   | pos
--   | neg

-- def posOrNegThree (a : SignC) : (match (a : SignC) with | SignC.pos => Nat | SignC.neg => Int) :=
--   match a with
--   | SignC.pos => 3
--   | SignC.neg => -3

-- #eval posOrNegThree (SignC.neg)


-- inductive ListC (α: Type) where
--   | nil
--   | const (n : α) (l : (ListC α)) : (ListC α)

-- def test := ListC.const 2 (ListC.const 1 ListC.nil)


-- def length {α : Type} (l : ListC α) : Nat :=
--   match l with
--   | ListC.nil => 0
--   | ListC.const _ l => 1 + length l

-- #eval length test

-- structure ProdC {α β : Type} where
--   fst : α
--   snd : β

-- inductive SumC (α β: Type) where
--   | inl (a : α) : SumC α β
--   | inr (b : β) : SumC α β

-- #eval (SumC.inr 1 : (SumC Nat Nat))

-- #check Option.none
-- #check Option.some 1

-- def last_list (α : Type) (l : List α) : Option α :=
--   match l with
--   | [] => Option.none
--   | [(a : α)] => Option.some a
--   | _ :: ak => last_list α ak

-- #eval last_list Nat ([1,2,3,4,5,6] : List Nat)

-- def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
--   match xs with
--   | [] => Option.none
--   | (a :: ak) => if predicate a then (Option.some a) else List.findFirst? ak predicate

--  def Prod.switch {α β : Type} (pair : α × β) : β × α :=
--   Prod.mk pair.2 pair.1


-- def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
--   match xs with
--   | [] => []
--   | a :: x =>
--     match ys with
--     | [] => []
--     | b :: y => List.cons (Prod.mk a b) (zip x y)

-- #eval zip ([1, 2,3]) ([1,2, 2,2])

-- def first_n {α : Type} (l : List α) (n : ℕ) :=
--   match n with
--   | 0 => []
--   | Nat.succ k =>
--     match l with
--     | [] => []
--     | xs :: x => List.cons xs (first_n x k)

-- #eval first_n [1,2,3,4] 3

-- def product_over_sums (α β γ : Type) (a : α × (β ⊕ γ)) : (α ⊕ β) × (α ⊕ γ) :=
--   Prod.mk (Sum.inl a.1) (Sum.inl a.1)

-- def test_2 (α : Type) (a : Bool × α) : α ⊕ α :=
--   Sum.inl a.2

-- def unzip {α β : Type} : List (α × β) → List α × List β
--   | [] => ([], [])
--   | (a, b) :: xab =>
--     let prev := unzip xab
--     (a :: prev.1, b :: prev.2)

-- #eval unzip [(1,2), (2,4)]

-- def reverse (xs : List α) : List α :=
--   let rec helper : List α → List α → List α
--   | [], l => l
--   | a :: al, l => helper al (a :: l)
--   helper xs []

-- #eval reverse [1,2,3]



-- inductive even : Type where
--   | zero : even
--   | succ : even → even


-- instance : HAdd even even even where
--   hAdd a b :=
--     let rec AddEven (n : even): even → even
--       | even.zero => n
--       | even.succ k => AddEven (n) k
--     AddEven a b

-- instance : HMul even even even where
--   hMul a b :=
--     let rec MulEven (n : even) : even → even
--       | even.zero => even.zero
--       | even.succ k => even.succ (MulEven n k)
--     MulEven a b




-- class IsEven (α : Type) where
--   iseven : α → Bool

-- instance : IsEven Nat where
--   iseven (n : Nat) := IsEvenNat n



-- instance : OfNat even 0 where
--   ofNat := even.zero

-- instance [OfNat even n] : OfNat even (Nat.succ (Nat.succ n)) where
--   ofNat := even.succ (OfNat.ofNat n)

-- structure PPoint (α : Type) where
--   x : α
--   y : α

-- instance {α : Type} [Mul α] : HMul (PPoint α) α (PPoint α) where
--   hMul p k := ⟨p.x * k, p.y * k⟩

-- #eval (⟨1,2⟩ : PPoint Nat) * 12

-- #eval (⟨1,1⟩ : PPoint Nat)


-- variable (α : Type)

-- inductive BinTree (α : Type) where
--   | leaf : BinTree α
--   | branch : BinTree α → α → BinTree α → BinTree α

-- def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
--   | BinTree.leaf, BinTree.leaf =>
--     true
--   | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
--     x == x2 && eqBinTree l l2 && eqBinTree r r2
--   | _, _ =>
--     false

-- instance [BEq α] : BEq (BinTree α) where
--   beq := eqBinTree

-- instance : BEq (BinTree Nat) where
--   beq :=
--     let rec eqchecker : (t1 : BinTree Nat) → (t2 : BinTree Nat) → Bool
--     | BinTree.leaf, BinTree.leaf => True
--     | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
--     x == x2 && eqchecker l l2 && eqchecker r2 r
--     | _, _ => False

--   λ a b => eqchecker a b






-- -- instance [IsEven Nat]: OfNat even (n : Nat) where
-- --   ofNat :=
-- --     let rec NatToEven : Nat → even
-- --       | 0 => even.zero
-- --       | Nat.succ (Nat.succ n) => even.succ (NatToEven n)
-- --     NatToEven n



-- abbrev BoolInput (n : ℕ) := Fin n → Bool

-- -- #check { x : ℝ | x < 5}

-- def BoolFunction (n : ℕ) := BoolInput n → Bool


-- variable {n : ℕ}

-- example : BoolFunction 2 :=
--   fun a => a 0 ∨ a 1

-- -- #check Finset.univ.filter _
-- def hammingWeight (x : BoolInput n) : ℕ :=
--   (Finset.univ.filter (fun i => x i)).card



-- inductive DecisionTree (n : ℕ) where
--   | leaf (val : Bool) : DecisionTree n
--   | node (i : Fin n) (left : DecisionTree n) (right : DecisionTree n) : DecisionTree n

-- def eval (t : DecisionTree n) (x : BoolInput n) : Bool :=
--   match t with
--   | DecisionTree.leaf val => val
--   | DecisionTree.node i left right => if x i then (eval right x) else (eval left x)

-- def computes (t : DecisionTree n) (f : BoolFunction n) : Prop :=
--   ∀ (x : BoolInput n), eval t x = f x

-- -- def All_Paths (t : BinaryTree α) : List (List α) :=
-- --   match t with
-- --   | BinaryTree.leaf => [[]]
-- --   | BinaryTree.node l x r => ( [x] (All_Paths l).flatten) ++ (x :: (All_Paths r).flatten)

-- def depth (t : DecisionTree n) : ℕ :=
--   match t with
--   | DecisionTree.leaf _ => 0
--   | DecisionTree.node _ l r => 1 + max (depth l) (depth r)


-- noncomputable def DecisionTreeComplexity (f : BoolFunction n) : ℕ :=
--   sInf { d | ∃ t : DecisionTree n, computes t f ∧ depth t = d }



-- #min_imports

-- -- def sensitivity (t : DecisionTree α) : Nat := sorry

-- -- def Depth (t : DecisionTree α) : Nat :=
-- --   match t with
-- --   | DecisionTree.leaf => 0
-- --   | DecisionTree.node l _ r => 1 + max (Depth l) (Depth r)


import Mathlib

-- even is a function from ℕ to prop, where there are two ways of constructing this predicate
inductive Even_cool : ℕ → Prop where
  | zero : Even_cool 0
  | add_two : ∀ k : ℕ, Even_cool k → Even_cool (k+2)


theorem Even_4 : Even_cool 4 :=
  have Even_0 : Even_cool 0 := Even_cool.zero
  have Even_2 : Even_cool 2 := Even_cool.add_two 0 Even_0
  have Even_4 : Even_cool 4 := Even_cool.add_two 2 Even_2
  Even_4

def evenRec : ℕ → Prop
  | 0 => true
  | 1 => false
  | k + 2 => evenRec k

example (n : ℕ) (ne : Even_cool n) : ¬Even_cool (n+1) := by
  induction ne
  ·
    intro h
    cases h
  ·
    intro h
    cases h
    contradiction
























  -- apply le_add_of_sub_right_le
  -- apply abs_add_le (a - b) (b)
