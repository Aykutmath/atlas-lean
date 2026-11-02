import OrthogonalPinching
import OperatorFrobeniusEquiv

noncomputable section
open MeasureTheory Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid

/-- Padding by two Euclidean isometries preserves the actual spectral nuclear norm. -/
theorem spectralNuclear_isometric_padding {r q h k : ℕ}
    (U : Euclid r →L[ℝ] Euclid h) (V : Euclid q →L[ℝ] Euclid k)
    (T : Euclid q →L[ℝ] Euclid r)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hUi : ContinuousLinearMap.adjoint U ∘L U = ContinuousLinearMap.id ℝ _)
    (hVi : ContinuousLinearMap.adjoint V ∘L V = ContinuousLinearMap.id ℝ _) :
    spectralNuclearNorm (operatorFrobenius (U ∘L T ∘L ContinuousLinearMap.adjoint V)) =
      spectralNuclearNorm (operatorFrobenius T) := by
  apply le_antisymm
  · exact spectralNuclear_compression_le U T (ContinuousLinearMap.adjoint V) hU (by simpa using hV)
  · have hh := spectralNuclear_compression_le (ContinuousLinearMap.adjoint U)
      (U ∘L T ∘L ContinuousLinearMap.adjoint V) V (by simpa using hU) hV
    have hid : ContinuousLinearMap.adjoint U ∘L
        (U ∘L T ∘L ContinuousLinearMap.adjoint V) ∘L V = T := by
      calc
        _ = (ContinuousLinearMap.adjoint U ∘L U) ∘L T ∘L
            (ContinuousLinearMap.adjoint V ∘L V) := by simp only [ContinuousLinearMap.comp_assoc]
        _ = T := by rw [hUi, hVi]; simp
    rwa [hid] at hh

theorem euclid_sum_apply {ι : Type*} [Fintype ι] {h : ℕ}
    (f : ι → Euclid h) (i : Fin h) : (∑ j, f j) i = ∑ j, f j i := by
  exact map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin h => ℝ) i) f Finset.univ

/-- Insert Euclidean coordinates along an injection, zero elsewhere. -/
def coordinateEmbedding {r h : ℕ} (e : Fin r ↪ Fin h) : Euclid r →L[ℝ] Euclid h :=
  (show Euclid r →ₗ[ℝ] Euclid h from
    { toFun := fun x => ∑ i, x i • EuclideanSpace.single (e i) (1 : ℝ)
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [mul_smul, Finset.smul_sum] }).toContinuousLinearMap

@[simp] theorem coordinateEmbedding_apply {r h : ℕ} (e : Fin r ↪ Fin h) (x : Euclid r) :
    coordinateEmbedding e x = ∑ i, x i • EuclideanSpace.single (e i) (1 : ℝ) := rfl

theorem coordinateEmbedding_norm {r h : ℕ} (e : Fin r ↪ Fin h) (x : Euclid r) :
    ‖coordinateEmbedding e x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [coordinateEmbedding_apply]
  have ho : Orthonormal ℝ (fun i : Fin r => EuclideanSpace.single (e i) (1 : ℝ)) := by
    simpa only [Function.comp_def, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal.comp e e.injective
  rw [norm_orthogonal_sum_sq _ (fun i j hij => ho.2 hij), PiLp.norm_sq_eq_of_L2]
  simp only [ho.1, one_pow, mul_one, Real.norm_eq_abs, sq_abs]

theorem coordinateEmbedding_norm_le_one {r h : ℕ} (e : Fin r ↪ Fin h) :
    ‖coordinateEmbedding e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, coordinateEmbedding_norm]

@[simp] theorem coordinateEmbedding_adjoint_apply {r h : ℕ} (e : Fin r ↪ Fin h)
    (x : Euclid h) (i : Fin r) :
    (ContinuousLinearMap.adjoint (coordinateEmbedding e) x) i = x (e i) := by
  have hi := ContinuousLinearMap.adjoint_inner_right (coordinateEmbedding e)
    (EuclideanSpace.single i (1 : ℝ)) x
  have hb : coordinateEmbedding e (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (e i) (1 : ℝ) := by
    simp [coordinateEmbedding_apply, EuclideanSpace.single_apply]
  rw [hb] at hi
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, conj_trivial] using hi

@[simp] theorem coordinateEmbedding_entry {r h : ℕ} (e : Fin r ↪ Fin h)
    (x : Euclid r) (i : Fin r) : coordinateEmbedding e x (e i) = x i := by
  simp only [coordinateEmbedding_apply, euclid_sum_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, e.injective.eq_iff]
  simp

theorem coordinateEmbedding_adjoint_comp {r h : ℕ} (e : Fin r ↪ Fin h) :
    ContinuousLinearMap.adjoint (coordinateEmbedding e) ∘L coordinateEmbedding e =
      ContinuousLinearMap.id ℝ _ := by
  ext x i
  change (ContinuousLinearMap.adjoint (coordinateEmbedding e) (coordinateEmbedding e x)) i = x i
  rw [coordinateEmbedding_adjoint_apply, coordinateEmbedding_entry]

theorem coordinateEmbedding_cross_zero {J r h : ℕ} (e : Fin J × Fin r ↪ Fin h)
    (i j : Fin J) (hij : i ≠ j) :
    ContinuousLinearMap.adjoint (coordinateEmbedding ⟨fun a => e (i,a),
      fun _ _ hab => (Prod.mk.inj (e.injective hab)).2⟩) ∘L
      coordinateEmbedding ⟨fun a => e (j,a),
      fun _ _ hab => (Prod.mk.inj (e.injective hab)).2⟩ = 0 := by
  ext x a
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    coordinateEmbedding_adjoint_apply, ContinuousLinearMap.zero_apply, PiLp.zero_apply]
  simp only [coordinateEmbedding_apply, euclid_sum_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply]
  apply Finset.sum_eq_zero
  intro b _
  have hne : e (j,b) ≠ e (i,a) := fun hh => hij (Prod.mk.inj (e.injective hh)).1.symm
  simp only [Function.Embedding.coeFn_mk, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
  intro hh
  change e (i, a) = e (j, b) at hh
  exact (hne hh.symm).elim

/-- The coordinate insertion, bundled as a genuine Euclidean linear isometry. -/
def coordinateEmbeddingLinearIsometry {r h : ℕ} (e : Fin r ↪ Fin h) :
    Euclid r →ₗᵢ[ℝ] Euclid h where
  toLinearMap := (coordinateEmbedding e).toLinearMap
  norm_map' := coordinateEmbedding_norm e

/-- Restrict a product-indexed coordinate injection to one block. -/
def coordinateSlice {J r h : ℕ} (e : Fin J × Fin r ↪ Fin h) (j : Fin J) :
    Fin r ↪ Fin h :=
  ⟨fun a => e (j, a), fun _ _ hab => (Prod.mk.inj (e.injective hab)).2⟩

@[simp] theorem coordinateSlice_apply {J r h : ℕ} (e : Fin J × Fin r ↪ Fin h)
    (j : Fin J) (a : Fin r) : coordinateSlice e j a = e (j, a) := rfl

@[simp] theorem coordinateEmbedding_basis {r h : ℕ} (e : Fin r ↪ Fin h) (i : Fin r) :
    coordinateEmbedding e (EuclideanSpace.basisFun (Fin r) ℝ i) =
      EuclideanSpace.basisFun (Fin h) ℝ (e i) := by
  simp [coordinateEmbedding_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply]

/-- The orthogonal projection onto an isometrically embedded Euclidean space. -/
def embeddingProjection {r h : ℕ} (U : Euclid r →L[ℝ] Euclid h) :
    Euclid h →L[ℝ] Euclid h := U ∘L ContinuousLinearMap.adjoint U

@[simp] theorem embeddingProjection_selfadjoint {r h : ℕ}
    (U : Euclid r →L[ℝ] Euclid h) :
    ContinuousLinearMap.adjoint (embeddingProjection U) = embeddingProjection U := by
  simp [embeddingProjection]

theorem embeddingProjection_idempotent {r h : ℕ}
    (U : Euclid r →L[ℝ] Euclid h)
    (hU : ContinuousLinearMap.adjoint U ∘L U = ContinuousLinearMap.id ℝ _) :
    embeddingProjection U ∘L embeddingProjection U = embeddingProjection U := by
  calc
    _ = U ∘L (ContinuousLinearMap.adjoint U ∘L U) ∘L ContinuousLinearMap.adjoint U := by
      simp only [embeddingProjection, ContinuousLinearMap.comp_assoc]
    _ = embeddingProjection U := by simp [hU, embeddingProjection]

theorem embeddingProjection_orthogonal {r h : ℕ}
    (U V : Euclid r →L[ℝ] Euclid h)
    (hUV : ContinuousLinearMap.adjoint U ∘L V = 0) :
    embeddingProjection U ∘L embeddingProjection V = 0 := by
  calc
    _ = U ∘L (ContinuousLinearMap.adjoint U ∘L V) ∘L ContinuousLinearMap.adjoint V := by
      simp only [embeddingProjection, ContinuousLinearMap.comp_assoc]
    _ = 0 := by simp [hUV]

/-- Nuclear pinching for rectangular blocks identified by orthogonal isometries. -/
theorem sum_spectralNuclear_isometric_blocks_le {ι : Type*} [Fintype ι]
    {r q h k : ℕ} (T : Euclid k →L[ℝ] Euclid h)
    (U : ι → Euclid r →L[ℝ] Euclid h) (V : ι → Euclid q →L[ℝ] Euclid k)
    (hU : ∀ i, ‖U i‖ ≤ 1) (hV : ∀ i, ‖V i‖ ≤ 1)
    (hUi : ∀ i, ContinuousLinearMap.adjoint (U i) ∘L U i = ContinuousLinearMap.id ℝ _)
    (hVi : ∀ i, ContinuousLinearMap.adjoint (V i) ∘L V i = ContinuousLinearMap.id ℝ _)
    (hUo : ∀ i j, i ≠ j → ContinuousLinearMap.adjoint (U i) ∘L U j = 0)
    (hVo : ∀ i j, i ≠ j → ContinuousLinearMap.adjoint (V i) ∘L V j = 0) :
    ∑ i, spectralNuclearNorm
      (operatorFrobenius (ContinuousLinearMap.adjoint (U i) ∘L T ∘L V i)) ≤
        spectralNuclearNorm (operatorFrobenius T) := by
  have hp := sum_spectralNuclear_compressions_le T
    (fun i => embeddingProjection (U i)) (fun i => embeddingProjection (V i))
    (fun i => embeddingProjection_selfadjoint (U i))
    (fun i => embeddingProjection_selfadjoint (V i))
    (fun i => embeddingProjection_idempotent (U i) (hUi i))
    (fun i => embeddingProjection_idempotent (V i) (hVi i))
    (fun i j hij => embeddingProjection_orthogonal (U i) (U j) (hUo i j hij))
    (fun i j hij => embeddingProjection_orthogonal (V i) (V j) (hVo i j hij))
  calc
    _ = ∑ i, spectralNuclearNorm (operatorFrobenius
        (embeddingProjection (U i) ∘L T ∘L embeddingProjection (V i))) := by
      apply Finset.sum_congr rfl
      intro i _
      have he := spectralNuclear_isometric_padding (U i) (V i)
        (ContinuousLinearMap.adjoint (U i) ∘L T ∘L V i)
        (hU i) (hV i) (hUi i) (hVi i)
      simpa only [embeddingProjection, ContinuousLinearMap.comp_assoc] using he.symm
    _ ≤ _ := hp

/-- Extract a rectangular diagonal coordinate block. Frobenius matrices are
column-first: the entry with row `a` and column `b` is `coordinateBlock ... j b a`. -/
def coordinateBlock {J r q h k : ℕ} (eL : Fin J × Fin r ↪ Fin h)
    (eR : Fin J × Fin q ↪ Fin k) (A : FrobeniusMatrix h k) (j : Fin J) :
    FrobeniusMatrix r q :=
  (WithLp.equiv 2 _).symm (fun b =>
    (WithLp.equiv 2 _).symm (fun a => A (eR (j, b)) (eL (j, a))))

@[simp] theorem coordinateBlock_apply {J r q h k : ℕ}
    (eL : Fin J × Fin r ↪ Fin h) (eR : Fin J × Fin q ↪ Fin k)
    (A : FrobeniusMatrix h k) (j : Fin J) (a : Fin r) (b : Fin q) :
    coordinateBlock eL eR A j b a = A (eR (j, b)) (eL (j, a)) := rfl

/-- Entry extraction is precisely two-sided compression by coordinate isometries. -/
theorem coordinateBlock_eq_compression {J r q h k : ℕ}
    (eL : Fin J × Fin r ↪ Fin h) (eR : Fin J × Fin q ↪ Fin k)
    (A : FrobeniusMatrix h k) (j : Fin J) :
    coordinateBlock eL eR A j = operatorFrobenius
      (ContinuousLinearMap.adjoint (coordinateEmbedding (coordinateSlice eL j)) ∘L
        frobeniusOperator A ∘L coordinateEmbedding (coordinateSlice eR j)) := by
  ext b a
  simp only [coordinateBlock_apply, operatorFrobenius_apply,
    ContinuousLinearMap.comp_apply, coordinateEmbedding_basis,
    coordinateEmbedding_adjoint_apply, coordinateSlice_apply, frobeniusOperator_basis]

/-- Padding an extracted block is exactly the corresponding two-sided ambient
orthogonal projection. -/
theorem coordinateBlock_padded_eq_projections {J r q h k : ℕ}
    (eL : Fin J × Fin r ↪ Fin h) (eR : Fin J × Fin q ↪ Fin k)
    (A : FrobeniusMatrix h k) (j : Fin J) :
    coordinateEmbedding (coordinateSlice eL j) ∘L
        frobeniusOperator (coordinateBlock eL eR A j) ∘L
        ContinuousLinearMap.adjoint (coordinateEmbedding (coordinateSlice eR j)) =
      embeddingProjection (coordinateEmbedding (coordinateSlice eL j)) ∘L
        frobeniusOperator A ∘L
        embeddingProjection (coordinateEmbedding (coordinateSlice eR j)) := by
  rw [coordinateBlock_eq_compression, frobeniusOperator_operatorFrobenius]
  simp only [embeddingProjection, ContinuousLinearMap.comp_assoc]

/-- The small coordinate block and its ambient projected version have exactly
the same spectral nuclear norm. -/
theorem spectralNuclear_coordinateBlock_eq_projected {J r q h k : ℕ}
    (eL : Fin J × Fin r ↪ Fin h) (eR : Fin J × Fin q ↪ Fin k)
    (A : FrobeniusMatrix h k) (j : Fin J) :
    spectralNuclearNorm (coordinateBlock eL eR A j) =
      spectralNuclearNorm (operatorFrobenius
        (embeddingProjection (coordinateEmbedding (coordinateSlice eL j)) ∘L
          frobeniusOperator A ∘L
          embeddingProjection (coordinateEmbedding (coordinateSlice eR j)))) := by
  rw [← coordinateBlock_padded_eq_projections]
  rw [spectralNuclear_isometric_padding _ _ _
    (coordinateEmbedding_norm_le_one _) (coordinateEmbedding_norm_le_one _)
    (coordinateEmbedding_adjoint_comp _) (coordinateEmbedding_adjoint_comp _)]
  rw [operatorFrobenius_frobeniusOperator]

/-- The sum of the genuine spectral nuclear norms of disjoint coordinate blocks
is at most the genuine spectral nuclear norm of the original rectangular matrix. -/
theorem sum_spectralNuclear_coordinateBlock_le {J r q h k : ℕ}
    (eL : Fin J × Fin r ↪ Fin h) (eR : Fin J × Fin q ↪ Fin k)
    (A : FrobeniusMatrix h k) :
    ∑ j, spectralNuclearNorm (coordinateBlock eL eR A j) ≤ spectralNuclearNorm A := by
  simpa only [coordinateBlock_eq_compression, operatorFrobenius_frobeniusOperator] using
    sum_spectralNuclear_isometric_blocks_le (frobeniusOperator A)
      (fun j => coordinateEmbedding (coordinateSlice eL j))
      (fun j => coordinateEmbedding (coordinateSlice eR j))
      (fun j => coordinateEmbedding_norm_le_one (coordinateSlice eL j))
      (fun j => coordinateEmbedding_norm_le_one (coordinateSlice eR j))
      (fun j => coordinateEmbedding_adjoint_comp (coordinateSlice eL j))
      (fun j => coordinateEmbedding_adjoint_comp (coordinateSlice eR j))
      (fun i j hij => coordinateEmbedding_cross_zero eL i j hij)
      (fun i j hij => coordinateEmbedding_cross_zero eR i j hij)

end GaussianEllipsoid
#print axioms GaussianEllipsoid.spectralNuclear_isometric_padding
#print axioms GaussianEllipsoid.sum_spectralNuclear_isometric_blocks_le
#print axioms GaussianEllipsoid.sum_spectralNuclear_coordinateBlock_le

