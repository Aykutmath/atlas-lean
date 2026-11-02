import VolumetricNets
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open Set Metric Module
open scoped BigOperators

namespace GaussianEllipsoid

/-- Real rectangular matrices represented by their Euclidean columns. This is the
Frobenius norm, not the default supremum norm on a function-valued matrix. -/
abbrev FrobeniusMatrix (r q : ℕ) :=
  PiLp 2 (fun _ : Fin q => EuclideanSpace ℝ (Fin r))

/-- Left multiplication of Euclidean columns by a genuine operator-norm map. -/
def leftAction {r k q : ℕ}
    (U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C : FrobeniusMatrix k q) : FrobeniusMatrix r q :=
  (WithLp.equiv 2 _).symm (fun j => U (C j))

@[simp] theorem leftAction_apply {r k q : ℕ}
    (U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C : FrobeniusMatrix k q) (j : Fin q) : leftAction U C j = U (C j) := rfl

theorem finrank_frobenius (r q : ℕ) : finrank ℝ (FrobeniusMatrix r q) = r * q := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin q → EuclideanSpace ℝ (Fin r))).finrank_eq]
  simp [Module.finrank_pi_fintype, Nat.mul_comm]

/-- The operator/Frobenius ideal inequality, with constant exactly one. -/
theorem norm_leftAction_le {r k q : ℕ}
    (U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C : FrobeniusMatrix k q) : ‖leftAction U C‖ ≤ ‖U‖ * ‖C‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [leftAction_apply, ← mul_pow] using
    pow_le_pow_left₀ (norm_nonneg (U (C j))) (U.le_opNorm (C j)) 2

@[simp] theorem leftAction_sub_left {r k q : ℕ}
    (U V : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C : FrobeniusMatrix k q) : leftAction (U - V) C = leftAction U C - leftAction V C := by
  ext j i
  rfl

@[simp] theorem leftAction_sub_right {r k q : ℕ}
    (U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C D : FrobeniusMatrix k q) : leftAction U (C - D) = leftAction U C - leftAction U D := by
  ext j i
  simp [leftAction]

/-- Two-factor telescoping in Frobenius norm. -/
theorem norm_leftAction_sub_le {r k q : ℕ}
    (U V : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (C D : FrobeniusMatrix k q) :
    ‖leftAction U C - leftAction V D‖ ≤ ‖U - V‖ * ‖C‖ + ‖V‖ * ‖C - D‖ := by
  have hid : leftAction U C - leftAction V D =
      leftAction (U - V) C + leftAction V (C - D) := by
    simp only [leftAction_sub_left, leftAction_sub_right]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add (norm_leftAction_le _ _) (norm_leftAction_le _ _))


/-- A cover of all `U*C` with `‖U‖op ≤ 1` and `‖C‖F ≤ R`.
The parameter count is `r*k + k*q`; this avoids a singular-value decomposition. -/
theorem exists_factorized_frobenius_cover (r k q : ℕ) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r q),
      (∀ A ∈ s, ‖A‖ ≤ R) ∧
      (s.card : ℝ) ≤ (1 + 4 * R / ε) ^ (r * k + k * q) ∧
      (∀ U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r),
        ‖U‖ ≤ 1 → ∀ C : FrobeniusMatrix k q, ‖C‖ ≤ R →
        ∃ B ∈ s, ‖leftAction U C - B‖ < ε) := by
  classical
  let η : ℝ := ε / (2 * R)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨u, hu, hucard, hunet⟩ := exists_operator_unit_net r k
    {U | ‖U‖ ≤ 1} hη (fun U hU => hU)
  obtain ⟨c, hc, hccard, hcnet, _⟩ := exists_internal_net
    {C : FrobeniusMatrix k q | ‖C‖ ≤ R}
    hR.le (half_pos hε) (fun C hC => hC)
  let s := (u ×ˢ c).image (fun p => leftAction p.1 p.2)
  have hbaseU : 1 + 2 / η = 1 + 4 * R / ε := by
    dsimp [η]
    field_simp
    ring
  have hbaseC : 1 + 2 * R / (ε / 2) = 1 + 4 * R / ε := by ring
  refine ⟨s, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨⟨U, C⟩, hUC, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hU, hC⟩ := Finset.mem_product.mp hUC
    exact (norm_leftAction_le U C).trans
      ((mul_le_mul (hu U hU) (hc C hC) (norm_nonneg C) zero_le_one).trans_eq (one_mul R))
  · calc
      (s.card : ℝ) ≤ ((u ×ˢ c).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      _ = (u.card : ℝ) * (c.card : ℝ) := by rw [Finset.card_product]; norm_cast
      _ ≤ (1 + 2 / η) ^ (r * k) * (1 + 2 * R / (ε / 2)) ^ (k * q) := by
        apply mul_le_mul hucard
        · simpa only [finrank_frobenius] using hccard
        · positivity
        · positivity
      _ = (1 + 4 * R / ε) ^ (r * k + k * q) := by rw [hbaseU, hbaseC, pow_add]
  · intro U hU C hC
    obtain ⟨V, hV, hUV⟩ := hunet U hU
    obtain ⟨D, hD, hCD⟩ := hcnet C hC
    rw [dist_eq_norm] at hCD
    refine ⟨leftAction V D, Finset.mem_image.mpr ⟨(V, D), Finset.mem_product.mpr ⟨hV, hD⟩, rfl⟩, ?_⟩
    have hfirst : ‖U - V‖ * ‖C‖ < ε / 2 := by
      calc
        ‖U - V‖ * ‖C‖ ≤ ‖U - V‖ * R := mul_le_mul_of_nonneg_left hC (norm_nonneg _)
        _ < η * R := mul_lt_mul_of_pos_right hUV hR
        _ = ε / 2 := by dsimp [η]; field_simp
    have hsecond : ‖V‖ * ‖C - D‖ < ε / 2 := by
      exact (mul_le_mul_of_nonneg_right (hu V hV) (norm_nonneg _)).trans_lt
        (by simpa only [one_mul] using hCD)
    exact (norm_leftAction_sub_le U V C D).trans_lt (by linarith)


/-- Every real finite-dimensional inner product space of dimension at most `k`
embeds isometrically into Euclidean `k`-space. -/
theorem exists_euclidean_isometry {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ)
    (hk : finrank ℝ E ≤ k) : Nonempty (E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) := by
  let b := stdOrthonormalBasis ℝ E
  let d := EuclideanSpace.basisFun (Fin k) ℝ
  let f : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    b.toBasis.constr ℝ (fun i => d (Fin.castLE hk i))
  have hf : Orthonormal ℝ (f ∘ b.toBasis) := by
    have hd := d.orthonormal.comp (Fin.castLE hk) (Fin.castLE_injective hk)
    simpa only [f, Function.comp_def, Basis.constr_basis] using hd
  exact ⟨f.isometryOfOrthonormal b.orthonormal hf⟩

/-- The ordinary column span; its finite dimension is matrix rank. -/
def columnSpan {r q : ℕ} (A : FrobeniusMatrix r q) :
    Submodule ℝ (EuclideanSpace ℝ (Fin r)) := Submodule.span ℝ (Set.range (fun j => A j))

/-- Low column-span rank yields an operator-contractive factorization without
inflating Frobenius norm. This replaces the SVD for the low-rank covering step. -/
theorem exists_contractive_factorization {r k q : ℕ} (A : FrobeniusMatrix r q)
    (hRank : finrank ℝ (columnSpan A) ≤ k) :
    ∃ U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r),
      ∃ C : FrobeniusMatrix k q, ‖U‖ ≤ 1 ∧ ‖C‖ = ‖A‖ ∧ leftAction U C = A := by
  let S := columnSpan A
  have hmem (j : Fin q) : A j ∈ S := Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨J⟩ := exists_euclidean_isometry (E := S) k hRank
  let U : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    S.subtypeL.comp (ContinuousLinearMap.adjoint J.toContinuousLinearMap)
  let C : FrobeniusMatrix k q := (WithLp.equiv 2 _).symm
    (fun j => J ⟨A j, hmem j⟩)
  have hU : ‖U‖ ≤ 1 := by
    calc
      ‖U‖ ≤ ‖S.subtypeL‖ * ‖ContinuousLinearMap.adjoint J.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul S.norm_subtypeL_le
        (by simpa only [ContinuousLinearMap.adjoint.norm_map] using J.norm_toContinuousLinearMap_le)
        (norm_nonneg (ContinuousLinearMap.adjoint J.toContinuousLinearMap)) zero_le_one
      _ = 1 := one_mul 1
  have hC : ‖C‖ = ‖A‖ := by
    rw [PiLp.norm_eq_of_L2 C, PiLp.norm_eq_of_L2 A]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change ‖J ⟨A j, hmem j⟩‖ ^ 2 = ‖A j‖ ^ 2
    rw [J.norm_map]
    rfl
  have hJU := J.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp J.norm_map
  refine ⟨U, C, hU, hC, ?_⟩
  ext j i
  have hx := congrArg (fun L : S →L[ℝ] S => L ⟨A j, hmem j⟩) hJU
  change (ContinuousLinearMap.adjoint J.toContinuousLinearMap (J ⟨A j, hmem j⟩)).val i = A j i
  exact congrArg (fun x : S => x.val i) hx


/-- Coordinates as an ordinary rectangular `Matrix`. This conversion does not use
that matrix type's norm. -/
def frobeniusToMatrix {r q : ℕ} (A : FrobeniusMatrix r q) : Matrix (Fin r) (Fin q) ℝ :=
  fun i j => A j i

/-- Column-span rank agrees exactly with Mathlib's standard matrix rank. -/
theorem rank_frobeniusToMatrix {r q : ℕ} (A : FrobeniusMatrix r q) :
    (frobeniusToMatrix A).rank = finrank ℝ (columnSpan A) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  let e := WithLp.linearEquiv 2 ℝ (Fin r → ℝ)
  have heq : Submodule.span ℝ (Set.range (frobeniusToMatrix A).col) =
      (columnSpan A).map e.toLinearMap := by
    rw [columnSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [heq]
  exact e.finrank_map_eq (columnSpan A)

/-- Low-rank rectangular matrices have a Frobenius ε-cover of the expected
intrinsic parameter count, with the stronger constant `4` in the covering base. -/
theorem exists_lowRank_frobenius_cover (r k q : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r q),
      (∀ B ∈ s, ‖B‖ ≤ R) ∧
      (s.card : ℝ) ≤ (1 + 4 * R / ε) ^ (r * k + k * q) ∧
      (∀ A : FrobeniusMatrix r q, (frobeniusToMatrix A).rank ≤ k → ‖A‖ ≤ R →
        ∃ B ∈ s, ‖A - B‖ < ε) := by
  classical
  rcases hR.eq_or_lt with hR | hR
  · subst R
    refine ⟨{0}, by simp, by simp, ?_⟩
    intro A _ hA
    have hA0 : A = 0 := norm_eq_zero.mp (le_antisymm hA (norm_nonneg _))
    exact ⟨0, by simp, by simpa [hA0] using hε⟩
  · obtain ⟨s, hs, hcard, hnet⟩ := exists_factorized_frobenius_cover r k q hR hε
    refine ⟨s, hs, hcard, ?_⟩
    intro A hRank hA
    rw [rank_frobeniusToMatrix] at hRank
    obtain ⟨U, C, hU, hC, hUC⟩ := exists_contractive_factorization A hRank
    simpa only [hUC] using hnet U hU C (hC.trans_le hA)

/-- Square-matrix specialization: exponent `2*r*k`, without a `sqrt(k)` loss. -/
theorem exists_square_lowRank_frobenius_cover (r k : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r r),
      (∀ B ∈ s, ‖B‖ ≤ R) ∧
      (s.card : ℝ) ≤ (1 + 4 * R / ε) ^ (2 * r * k) ∧
      (∀ A : FrobeniusMatrix r r, (frobeniusToMatrix A).rank ≤ k → ‖A‖ ≤ R →
        ∃ B ∈ s, ‖A - B‖ < ε) := by
  simpa only [show r * k + k * r = 2 * r * k by ring] using
    exists_lowRank_frobenius_cover r k r hR hε


/-- Explicit entry formula certifying that the chosen matrix norm is Frobenius. -/
theorem frobenius_norm_sq {r q : ℕ} (A : FrobeniusMatrix r q) :
    ‖A‖ ^ 2 = ∑ j : Fin q, ∑ i : Fin r, (frobeniusToMatrix A i j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs, frobeniusToMatrix]

/-- The exact rank-k covering bound appearing in the mathematical proof, as a
corollary of the stronger two-factor bound. -/
theorem exists_rankK_frobenius_cover (r k : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r r),
      (∀ B ∈ s, ‖B‖ ≤ R) ∧
      (s.card : ℝ) ≤ (1 + 6 * R / ε) ^ ((2 * r + 1) * k) ∧
      (∀ A : FrobeniusMatrix r r, (frobeniusToMatrix A).rank ≤ k → ‖A‖ ≤ R →
        ∃ B ∈ s, ‖A - B‖ < ε) := by
  obtain ⟨s, hs, hcard, hnet⟩ := exists_square_lowRank_frobenius_cover r k hR hε
  refine ⟨s, hs, hcard.trans ?_, hnet⟩
  calc
    (1 + 4 * R / ε) ^ (2 * r * k) ≤ (1 + 6 * R / ε) ^ (2 * r * k) := by
      apply pow_le_pow_left₀ (by positivity)
      have : 4 * R ≤ 6 * R := by linarith
      exact add_le_add_right ((div_le_div_iff_of_pos_right hε).mpr this) 1
    _ ≤ (1 + 6 * R / ε) ^ ((2 * r + 1) * k) := by
      apply pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
      exact Nat.mul_le_mul_right k (Nat.le_add_right (2 * r) 1)

end GaussianEllipsoid

#print axioms GaussianEllipsoid.norm_leftAction_le
#print axioms GaussianEllipsoid.norm_leftAction_sub_le

#print axioms GaussianEllipsoid.exists_factorized_frobenius_cover

#print axioms GaussianEllipsoid.exists_euclidean_isometry
#print axioms GaussianEllipsoid.exists_contractive_factorization

#print axioms GaussianEllipsoid.rank_frobeniusToMatrix
#print axioms GaussianEllipsoid.exists_lowRank_frobenius_cover
#print axioms GaussianEllipsoid.exists_square_lowRank_frobenius_cover

#print axioms GaussianEllipsoid.frobenius_norm_sq
#print axioms GaussianEllipsoid.exists_rankK_frobenius_cover
