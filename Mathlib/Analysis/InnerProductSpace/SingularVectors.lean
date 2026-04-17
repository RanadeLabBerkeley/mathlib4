module

public import Mathlib

public section

variable (R : Type*) [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

open Submodule

/--
The span chain of an ordered family of vectors is the set of spans of initial segments.

For `ι = Fin n`:
Given a finite ordered list of vectors `v₀, v₁, v₂, ..., vₙ`, the span chain of v is the set
`{{0}, span(v₀), span(v₀, v₁), ..., span(v₀, v₁, ..., vₙ)}`.

For `ι = ℕ`:
Given a countable sequence of vectors `v₀, v₁, v₂, ...`, the span chain of v is the set
`{{0}, span(v₀), span(v₀, v₁), ..., span(v₀, v₁, v₂, ...)}`.
This includes the spans of every finite initial list of vectors as well as the span of the entire
sequence. In the case that `M` is a Hilbert space and `v₀, v₁, v₂, ...` is a Schauder basis, then
taking the closure of every element in the span chain produces a nest.
-/
def spanChain {ι : Type*} [LE ι] (v : ι → M) : Set (Submodule R M) :=
  {span R (v '' t) | t : LowerSet ι}

theorem mem_spanChain_iff {ι : Type*} [LE ι] (v : ι → M) (N : Submodule R M) :
    N ∈ spanChain R v ↔ ∃ t : Set ι, IsLowerSet t ∧ span R (v '' t) = N := by
  sorry

theorem span_mem_spanChain_of_isLowerSet {ι : Type*} [LE ι] (v : ι → M) {t : Set ι}
    (ht : IsLowerSet t) : span R (v '' t) ∈ spanChain R v := by
  rw [mem_spanChain_iff]
  use t

theorem span_image_Iio_mem_spanChain {ι : Type*} [Preorder ι] (v : ι → M) (i : ι) :
    span R (v '' Set.Iio i) ∈ spanChain R v :=
  span_mem_spanChain_of_isLowerSet R v (isLowerSet_Iio i)

theorem span_image_Iic_mem_spanChain {ι : Type*} [Preorder ι] (v : ι → M) (i : ι) :
    span R (v '' Set.Iic i) ∈ spanChain R v :=
  span_mem_spanChain_of_isLowerSet R v (isLowerSet_Iic i)

theorem bot_mem_spanChain {ι : Type*} [LE ι] (v : ι → M) : ⊥ ∈ spanChain R v := by
  simpa [spanChain] using Set.mem_range_self (f := fun t : LowerSet ι ↦ span R (v '' t))
    ⟨∅, isLowerSet_empty⟩

theorem span_range_mem_spanChain {ι : Type*} [LE ι] (v : ι → M) :
    span R (Set.range v) ∈ spanChain R v := by
  sorry

theorem isChain_spanChain {ι : Type*} [LinearOrder ι] (v : ι → M) :
    IsChain (· ≤ ·) (spanChain R v) :=
  sorry

/--
If `F` is a chain of submodules of `M` (or a partial flag), then an ordered family `v : ι → M`
is adapted to `F` iff ...
-/
structure IsAdaptedFamily {ι : Type*} [LE ι] (v : ι → M) (F : Set (Submodule R M)) where
  subset_spanChain : F ⊆ spanChain R v
