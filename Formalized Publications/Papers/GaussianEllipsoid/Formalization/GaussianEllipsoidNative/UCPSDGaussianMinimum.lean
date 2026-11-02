import UCPSDUnitGeometry
import UCPSDWidthUpper

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments MeasureTheory
namespace UCEscape
open BMGeometry

abbrev fullEntryMatrix {d : ℕ} (x : (Fin d × Fin d) → ℝ) : HMat d :=
  (frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x)

def psdMinimumRaw (d : ℕ) (x : (Fin d × Fin d) → ℝ) : ℝ :=
  sInf ((fun S => ⟪fullEntryMatrix x,S⟫_ℝ) '' psdUnit d)

theorem neg_support_le_psdMinimum {d : ℕ} (hd : 0 < d)
    (x : (Fin d × Fin d) → ℝ) :
    -gaussianPSDSupportRaw d (-x) ≤ psdMinimumRaw d x := by
  apply le_csInf ((psdUnit_nonempty hd).image _)
  rintro y ⟨S,hS,rfl⟩
  have h := fullEntry_pairing_le_psdSupport S hS (-x)
  have he : fullEntryMatrix (-x) = -fullEntryMatrix x := by
    change (frobeniusEquivEuclidean d d).symm (-((WithLp.equiv 2 _).symm x)) = _
    exact map_neg _ _
  change ⟪fullEntryMatrix (-x),S⟫_ℝ ≤ _ at h
  rw [he, inner_neg_left] at h
  linarith


def psdMinimum (d : ℕ) (A : HMat d) : ℝ :=
  sInf ((fun S => ⟪A,S⟫_ℝ) '' psdUnit d)

lemma psd_values_bddBelow (d : ℕ) (A : HMat d) :
    BddBelow ((fun S => ⟪A,S⟫_ℝ) '' psdUnit d) := by
  refine ⟨-‖A‖, ?_⟩
  rintro y ⟨S,hS,rfl⟩
  have hn : ‖S‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hS.2
  have h := (abs_le.mp (abs_real_inner_le_norm A S)).1
  simpa only [hn, mul_one] using h

lemma psdMinimum_sub_le (d : ℕ) (hd : 0 < d) (A B : HMat d) :
    psdMinimum d A - ‖A-B‖ ≤ psdMinimum d B := by
  apply le_csInf ((psdUnit_nonempty hd).image _)
  rintro y ⟨S,hS,rfl⟩
  have hi : psdMinimum d A ≤ ⟪A,S⟫_ℝ :=
    csInf_le (psd_values_bddBelow d A) ⟨S,hS,rfl⟩
  have hn : ‖S‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hS.2
  have hb := real_inner_le_norm (A-B) S
  rw [inner_sub_left, hn, mul_one] at hb
  linarith

theorem psdMinimum_lipschitz {d : ℕ} (hd : 0 < d) :
    LipschitzWith 1 (psdMinimum d) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  have h1 := psdMinimum_sub_le d hd A B
  have h2 := psdMinimum_sub_le d hd B A
  rw [norm_sub_rev B A] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms psdMinimum_lipschitz
#print axioms neg_support_le_psdMinimum
end UCEscape
