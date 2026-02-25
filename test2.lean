import Mathlib

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

structure MyGraph (V : Type u) where
  adj : V → V → Prop
  symm : Symmetric adj
  loopless : Irreflexive adj

def completeGraph (V : Type u) : MyGraph V := {
  adj := λ x y => x ≠ y
  symm := λ _ _ h => h.symm
  loopless := λ x h => h (show (x = x) by rfl)
}

namespace MyGraph

variable {G : MyGraph V} [DecidableRel G.adj]

def neighbors (v : V) : Finset V := Finset.univ.filter (G.adj v)

def degree (v : V) : ℕ := (G.neighbors v).card

#check degree

theorem degree_lt_vertices (v : V) : G.degree v < Fintype.card V := by sorry

def ProperOn (S : Finset V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ {x y}, x ∈ S → y ∈ S → G.adj x y → c x ≠ c y


-- def ProperOn.symm {S : Finset V} (k : ℕ) (c : V → Fin k) (h : G.ProperOn S k c) {x y : V}
--    ( hx : x ∈ S) (hy : y ∈ S) (hadj : G.adj) : c y ≠ c x := by sorry


set_option linter.unusedSectionVars false
lemma exists_color_not_in_neighbors (D : ℕ) (v : V) (c : V → Fin (D+1)) (hdeg : G.degree v ≤ D) :
  ∃ col : Fin (D+1), ∀ w ∈ G.neighbors v, col ≠ c w := by
  classical
  let forbidden : Finset (Fin (D+1)) := (G.neighbors v).image c
  have hforbid : forbidden.card ≤ D :=
    Finset.card_image_le.trans hdeg
  have hlt : forbidden.card < (Finset.univ : Finset (Fin (D+1))).card := by
    grind [Finset.card_fin]

  have first := Finset.exists_mem_notMem_of_card_lt_card hlt
  rcases first with ⟨col, _hcolU, hcolNot⟩

  refine ⟨col, ?_⟩
  intro w hwN

  have ww : c w ∈ forbidden := by
    exact Finset.mem_image.2 ⟨w, hwN, rfl⟩

  by_contra
  have w_2 : col ∈ forbidden := by simp [ww, this]
  exact hcolNot w_2

lemma extend_proper (D: ℕ) (S : Finset V) (v : V) (hv : v ∈ S)
(hdeg : ∀ w, G.degree w ≤ D) (hx : G.ProperOn (S.erase V) (D+1) c)
: ∃ c' : V → Fin (D+1) (hc : G.ProperOn S (D+1) c') := by
