module

public import Mathlib

public section

section inner_product

open Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]

def stdAdaptedOthonormalBasis {F : Set (Submodule 𝕜 V)} (hF : IsChain (· ≤ ·) F)
  : Fin (Module.finrank 𝕜 V) → V := sorry

/--
Note that the lists of singular vectors are allowed to continue on forever.
-/
structure LinearMap.SingularValueDecomposition (T : V →ₗ[𝕜] U) (u : ℕ → U) (v : ℕ → V) : Prop where
  -- This sum is always finite since T.singularValues eventually terminates
  decomposition : T = ∑ᶠ i, (T.singularValues i : 𝕜) • rankOne 𝕜 (u i) (v i)
  orthogonal_right {i j : ℕ} : i ≠ j → ⟪v i, v j⟫_𝕜 = 0
  orthogonal_left {i j : ℕ} : i ≠ j → ⟪u i, u j⟫_𝕜 = 0
  norm_right (i : ℕ) : ‖v i‖ = 1
  norm_left (i : ℕ) : ‖u i‖ = 1

def SingularValueDecomposition.ofEqOn {T : V →ₗ[𝕜] U} {u : ℕ → U} {v : ℕ → V}
    (hT : T.SingularValueDecomposition u v) {u' : ℕ → U} {v' : ℕ → V}
    (hu : Set.Iio (finrank 𝕜 T.range) |>.EqOn u u')
    (hv : Set.Iio (finrank 𝕜 T.range) |>.EqOn v v') : T.SingularValueDecomposition u' v' := by
  sorry

noncomputable def LinearMap.stdRightSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ V :=
  Finsupp.embDomain Fin.valEmbedding <|
    (Finsupp.ofSupportFinite (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl))
    (Set.toFinite _)

noncomputable def LinearMap.stdMinimalLeftSingularVectors (T : V →ₗ[𝕜] U) : ℕ →₀ U where
  support := sorry
  toFun (i : ℕ) := (1 / (T.singularValues i : 𝕜)) • T (T.stdRightSingularVectors i)
  mem_support_toFun := sorry

-- stdLeftSingularVectors

-- Should be able to derive that the stdLeft is singular values from the stdMinimal using the fact
-- that changing u and v on the parts where either the singular values are zero or the other is zero
-- doesn't affect it

end inner_product
