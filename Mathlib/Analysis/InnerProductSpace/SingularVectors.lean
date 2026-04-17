module

public import Mathlib

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {ι : Type*} [LE ι]

public section

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
def spanChain (v : ι → M) : Set (Submodule R M) :=
  {Submodule.span R (v '' t) | t : LowerSet ι}
