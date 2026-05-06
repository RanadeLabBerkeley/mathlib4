module

public import Mathlib

public section

section inner_product

open Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]

namespace LinearMap

/--
Note that the lists of singular vectors are allowed to continue on forever.
-/
structure SingularValueDecomposition (T : V →ₗ[𝕜] U) (u : ℕ → U) (v : ℕ → V) : Prop where
  -- This sum is always finite since T.singularValues eventually terminates
  decomposition : T = ∑ᶠ i, (T.singularValues i : 𝕜) • rankOne 𝕜 (u i) (v i)
  orthogonal_right {i j : ℕ} : i ≠ j → ⟪v i, v j⟫_𝕜 = 0
  orthogonal_left {i j : ℕ} : i ≠ j → ⟪u i, u j⟫_𝕜 = 0
  -- This might allow for "gaps" in certian cases.
  -- TODO: Figure out if this actually happens, which means determine what the minimum support of
  -- u and v is. Maybe support(u) ⊆ Iio (rank T) is forced.
  norm_right {i : ℕ} : v i ≠ 0 → ‖v i‖ = 1
  norm_left (i : ℕ) : u i ≠ 0 → ‖u i‖ = 1

theorem SingularValueDecomposition.adjoint {T : V →ₗ[𝕜] U} {u : ℕ → U} {v : ℕ → V}
    (hT : T.SingularValueDecomposition u v) : T.adjoint.SingularValueDecomposition v u := sorry

theorem SingularValueDecomposition.right_eqOn {T : V →ₗ[𝕜] U} {u : ℕ → U} {v : ℕ → V}
    (hT : T.SingularValueDecomposition u v) {v' : ℕ → V}
    (hv : Set.Iio (finrank 𝕜 T.range) |>.EqOn v v') : T.SingularValueDecomposition u v' := by
  sorry

theorem SingularValueDecomposition.left_eqOn {T : V →ₗ[𝕜] U} {u : ℕ → U} {v : ℕ → V}
    (hT : T.SingularValueDecomposition u v) {u' : ℕ → U}
    (hu : Set.Iio (finrank 𝕜 T.range) |>.EqOn u u') : T.SingularValueDecomposition u' v := by
  rw [← finrank_range_adjoint] at hu
  simpa using hT.adjoint.right_eqOn hu |>.adjoint

theorem SingularValueDecomposition.eqOn {T : V →ₗ[𝕜] U} {u : ℕ → U} {v : ℕ → V}
    (hT : T.SingularValueDecomposition u v) {u' : ℕ → U} {v' : ℕ → V}
    (hu : Set.Iio (finrank 𝕜 T.range) |>.EqOn u u')
    (hv : Set.Iio (finrank 𝕜 T.range) |>.EqOn v v') : T.SingularValueDecomposition u' v' :=
  hT.right_eqOn hv |>.left_eqOn hu

/-
There are three definitions of right singular vectors:
- `LinearMap.stdRightSingularOrthnormalBasis` - Singular vectors as an orthnormal basis
- `LinearMap.stdRightFullSingularVectors` - Same as `LinearMap.stdRightSingularOrthonormalBasis`,
but as a sequence `ℕ → V` which is eventually zero
- `LinearMap.stdRightCompactSingularVectors` - Same as `LinearMap.stdRightFullSingularVectors`, but
truncated to the first `rank(T)`.

Similarly, there are
- `LinearMap.stdLeftSingularOrthnormalBasis`
- `LinearMap.stdLeftFullSingularVectors`
- `LinearMap.stdLeftCompactSingularVectors`
for the left singular vectors.
-/

noncomputable def stdRightSingularOrthonormalBasis (T : V →ₗ[𝕜] U) :
    OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

noncomputable def stdRightFullSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ V :=
  Finsupp.embDomain Fin.valEmbedding <|
    (Finsupp.ofSupportFinite T.stdRightSingularOrthonormalBasis)
    (Set.toFinite _)

noncomputable def stdRightCompactSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ V :=
  T.stdRightFullSingularVectors.filter (· < finrank 𝕜 T.range)

noncomputable def stdLeftCompactSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ U where
  support := sorry
  toFun (i : ℕ) := (1 / (T.singularValues i : 𝕜)) • T (T.stdRightFullSingularVectors i)
  mem_support_toFun := sorry

-- TODO: Rename
private theorem helper (T : V →ₗ[𝕜] U)
  : Orthonormal 𝕜 <|
      (Set.Iio ⟨finrank 𝕜 T.range, sorry⟩).restrict
      (fun i : Fin (finrank 𝕜 U) => T.stdLeftCompactSingularVectors i) := sorry

noncomputable def stdLeftSingularOrthonormalBasis (T : V →ₗ[𝕜] U) :
    OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U :=
  Classical.choose <| T.helper.exists_orthonormalBasis_extension_of_card_eq
    (Fintype.card_fin _).symm

noncomputable def stdLeftFullSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ U :=
  Finsupp.embDomain Fin.valEmbedding <|
    (Finsupp.ofSupportFinite T.stdLeftSingularOrthonormalBasis)
    (Set.toFinite _)

-- Should be able to derive that the stdLeft is singular values from the stdCompact using eqOn

/-
Main singular value decomposition theorems
-/

theorem full_singularValueDecomposition (T : V →ₗ[𝕜] U) :
    T.SingularValueDecomposition T.stdLeftFullSingularVectors T.stdRightFullSingularVectors :=
  sorry

theorem compact_singularValueDecomposition (T : V →ₗ[𝕜] U) :
    T.SingularValueDecomposition T.stdLeftCompactSingularVectors T.stdRightCompactSingularVectors :=
  sorry

end LinearMap
end inner_product
