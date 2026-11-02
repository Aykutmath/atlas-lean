import GaussianPairedBlockLaw
import PolarDuality
import CoordinateBlockPinching

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall
open GaussianEllipsoidCandidate
open scoped ENNReal
namespace GaussianPairedBlocks

/-- Measurability of the paper-scaled actual bilinear observation. -/
theorem measurable_bilinearScaled (d : ℝ) (r n : ℕ) (w : Fin n → ℝ) :
    Measurable (bilinearScaled d r n w) := by
  unfold bilinearScaled
  exact (measurable_bilinearFrobenius r n w).const_smul (Real.sqrt (r:ℝ) / Real.sqrt d)

def flatBilinear (d : ℝ) (r n : ℕ) (w : Fin n → ℝ)
    (z : GaussianEntries n r × GaussianEntries n r) : FrobeniusMatrix r r :=
  bilinearScaled d r n w (flatToSmallBall n r z)

theorem measurable_flatBilinear (d : ℝ) (r n : ℕ) (w : Fin n → ℝ) :
    Measurable (flatBilinear d r n w) :=
  (measurable_bilinearScaled d r n w).comp (flatToSmallBall_measurable n r)

def blockThreshold (σ d : ℝ) (r : ℕ) : ℝ :=
  σ * (r : ℝ) * Real.sqrt (r : ℝ) / (1024 * Real.sqrt d)

/-- Uniform disjoint-head small ball at the exact block radius. -/
theorem flatBilinear_disjoint_smallball {r n s : ℕ} (hr : 0 < r) (hrs : r = 2*s)
    (u v : Fin n → ℝ) (hdisj : ∀ i, u i * v i = 0) {σ d : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hvsum : ∑ i, (v i)^2 = σ^2)
    (hvcap : ∀ i, (v i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹) :
    (tensorGaussianLaw n r).real
      {z | spectralNuclearNorm (flatBilinear d r n (u+v) z) ≤ blockThreshold σ d r}
      ≤ Real.exp (-(r*r:ℕ)) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsqr : 0 < Real.sqrt (r:ℝ) := Real.sqrt_pos.mpr hrR
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hT : 0 < blockThreshold σ d r := by unfold blockThreshold; positivity
  have h := gaussian_bilinear_disjoint_scaled_nuclear_smallball r n s hr hrs u v
    hdisj hσ hd hT hvsum hvcap
  have hbase : 160 * blockThreshold σ d r * Real.sqrt d /
      (σ * (r:ℝ) * Real.sqrt (r:ℝ)) = 160*(1/1024:ℝ) := by
    unfold blockThreshold
    field_simp
    <;> ring
  rw [hbase] at h
  have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hb : 160*(1/1024:ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 160*(1/1024:ℝ)) hb (r*r)
  rw [← Real.exp_nat_mul] at hp
  have hmeas : MeasurableSet {p | spectralNuclearNorm (bilinearScaled d r n (u+v) p) ≤
      blockThreshold σ d r} :=
    measurableSet_le ((continuous_spectralNuclear r r).measurable.comp
      (measurable_bilinearScaled d r n (u+v))) measurable_const
  have hmap := (flatToSmallBall_preserving n r).map_eq
  have hprob : (tensorGaussianLaw n r).real
      {z | spectralNuclearNorm (flatBilinear d r n (u+v) z) ≤ blockThreshold σ d r} =
      (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearScaled d r n (u+v) p) ≤ blockThreshold σ d r} := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply (flatToSmallBall_measurable n r) hmeas]
    rfl
  rw [hprob]
  convert h.trans hp using 1 <;> congr 1 <;> ring

/-- Conversion of an actual finite-measure real bound to an ENNReal bound. -/
theorem measure_le_of_real_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (E : Set Ω) {p : ℝ} (hp : μ.real E ≤ p) :
    μ E ≤ ENNReal.ofReal p := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
  exact ENNReal.ofReal_le_ofReal hp

/-- A sum smaller than half of J positive block thresholds forces at least
ceil(J/2) bad blocks. This deterministic step makes no probabilistic assumption. -/
theorem half_bad_of_sum_le {J : ℕ} (f : Fin J → ℝ) (hf : ∀ j, 0 ≤ f j)
    {T : ℝ} (hT : 0 < T) (h : ∑ j, f j ≤ (J:ℝ)/2*T) :
    (J+1)/2 ≤ (Finset.univ.filter fun j => f j ≤ T).card := by
  classical
  let B : Finset (Fin J) := Finset.univ.filter fun j => f j ≤ T
  let G : Finset (Fin J) := Finset.univ.filter fun j => ¬ f j ≤ T
  have hcard : B.card + G.card = J := by
    simpa only [B, G, Fintype.card_fin, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun j => f j ≤ T)
  have hsum : (G.card:ℝ)*T ≤ ∑ j, f j := by
    calc
      (G.card:ℝ)*T = ∑ _j ∈ G, T := by simp
      _ ≤ ∑ j ∈ G, f j := Finset.sum_le_sum (fun j hj => (lt_of_not_ge
        ((Finset.mem_filter.mp hj).2)).le)
      _ ≤ ∑ j, f j := Finset.sum_le_univ_sum_of_nonneg hf
  have hg : (G.card:ℝ) ≤ (J:ℝ)/2 := by nlinarith
  have hgn : 2*G.card ≤ J := by exact_mod_cast (show (2:ℝ)*G.card ≤ J by linarith)
  change (J+1)/2 ≤ B.card
  omega

/-- Elementary exponential majority amplification, valid for every positive even
r because then r²≥4 and exp(1)>2. -/
theorem exponential_majority_bound (J r : ℕ) (hr : 2 ≤ r) :
    (2:ℝ≥0∞)^J * (ENNReal.ofReal (Real.exp (-(r*r:ℕ))))^((J+1)/2) ≤
      ENNReal.ofReal (Real.exp (-(J:ℝ)*(r:ℝ)^2/4)) := by
  have he2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)
    linarith
  have hj : (J:ℝ)/2 ≤ ((J+1)/2:ℕ) := by
    have hn : J ≤ 2*((J+1)/2) := by omega
    have hh : (J:ℝ) ≤ 2*(((J+1)/2:ℕ):ℝ) := by exact_mod_cast hn
    linarith
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hr2 : (4:ℝ) ≤ (r:ℝ)^2 := by nlinarith
  have hreal : (2:ℝ)^J * (Real.exp (-(r*r:ℕ)))^((J+1)/2) ≤
      Real.exp (-(J:ℝ)*(r:ℝ)^2/4) := by
    calc
      _ ≤ (Real.exp 1)^J * (Real.exp (-(r*r:ℕ)))^((J+1)/2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he2 J) (by positivity)
      _ = Real.exp ((J:ℝ) - (((J+1)/2:ℕ):ℝ)*(r:ℝ)^2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hj0 : (0:ℝ) ≤ J := by positivity
        nlinarith [mul_nonneg hj0 (sub_nonneg.mpr hr2),
          mul_nonneg (sub_nonneg.mpr hj) (sq_nonneg (r:ℝ))]
  convert ENNReal.ofReal_le_ofReal hreal using 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by positivity)]
  norm_num

/-- Majority amplification for the sum of actual paired-block nuclear norms. -/
theorem paired_nuclear_sum_smallball {n h J r s : ℕ}
    (eL eR : Fin J × Fin r ↪ Fin h) (hr : 0 < r) (hrs : r = 2*s)
    (u v : Fin n → ℝ) (hdisj : ∀ i, u i * v i = 0) {σ d : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hvsum : ∑ i, (v i)^2 = σ^2)
    (hvcap : ∀ i, (v i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹) :
    tensorGaussianLaw n h
      {z | ∑ j, spectralNuclearNorm (flatBilinear d r n (u+v) (pairedBlock eL eR j z)) ≤
        (J:ℝ)/2 * blockThreshold σ d r} ≤
      ENNReal.ofReal (Real.exp (-(J:ℝ)*(r:ℝ)^2/4)) := by
  let E : Set (GaussianEntries n r × GaussianEntries n r) :=
    {z | spectralNuclearNorm (flatBilinear d r n (u+v) z) ≤ blockThreshold σ d r}
  have hE : MeasurableSet E := measurableSet_le
    ((continuous_spectralNuclear r r).measurable.comp (measurable_flatBilinear d r n (u+v)))
    measurable_const
  have hp : tensorGaussianLaw n r E ≤ ENNReal.ofReal (Real.exp (-(r*r:ℕ))) :=
    measure_le_of_real_le _ _ (flatBilinear_disjoint_smallball hr hrs u v hdisj hσ hd hvsum hvcap)
  have hT : 0 < blockThreshold σ d r := by
    have : (0:ℝ) < r := by exact_mod_cast hr
    unfold blockThreshold
    positivity
  have hsub : {z | ∑ j, spectralNuclearNorm (flatBilinear d r n (u+v) (pairedBlock eL eR j z)) ≤
      (J:ℝ)/2 * blockThreshold σ d r} ⊆
      {z | (J+1)/2 ≤ badCount (fun j => pairedBlock eL eR j ⁻¹' E) z} := by
    intro z hz
    exact half_bad_of_sum_le _ (fun _ => spectralNuclear_nonneg _) hT hz
  exact ((measure_mono hsub).trans
    (measure_many_paired_bad eL eR (fun _ => E) (fun _ => hE) _ (fun _ => hp) ((J+1)/2))).trans
    (exponential_majority_bound J r (by omega))

/-- Taking a paired coordinate block commutes with the actual bilinear matrix. -/
theorem coordinateBlock_flatBilinear {n h J r : ℕ}
    (eL eR : Fin J × Fin r ↪ Fin h) (hh : 0 < h) (hr : 0 < r)
    (d : ℝ) (w : Fin n → ℝ) (z : GaussianEntries n h × GaussianEntries n h) (j : Fin J) :
    coordinateBlock eL eR (flatBilinear d h n w z) j =
      flatBilinear d r n w (pairedBlock eL eR j z) := by
  ext b a
  change frobeniusToMatrix (flatBilinear d h n w z) (eL (j,a)) (eR (j,b)) =
    frobeniusToMatrix (flatBilinear d r n w (pairedBlock eL eR j z)) a b
  unfold flatBilinear
  rw [bilinearScaled_entry h n hh, bilinearScaled_entry r n hr]
  rfl

/-- Full actual-law paired-block amplification. Arbitrary disjoint coefficients
outside the capped driver are allowed, with no independence or law premises. -/
theorem paired_nuclear_smallball {n h J r s : ℕ}
    (eL eR : Fin J × Fin r ↪ Fin h) (hh : 0 < h) (hr : 0 < r) (hrs : r = 2*s)
    (u v : Fin n → ℝ) (hdisj : ∀ i, u i * v i = 0) {σ d : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hvsum : ∑ i, (v i)^2 = σ^2)
    (hvcap : ∀ i, (v i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (flatBilinear d h n (u+v) z) ≤
        (J:ℝ)/2 * blockThreshold σ d r} ≤
      ENNReal.ofReal (Real.exp (-(J:ℝ)*(r:ℝ)^2/4)) := by
  apply le_trans (measure_mono ?_)
    (paired_nuclear_sum_smallball eL eR hr hrs u v hdisj hσ hd hvsum hvcap)
  intro z hz
  have hp := sum_spectralNuclear_coordinateBlock_le eL eR (flatBilinear d h n (u+v) z)
  simp_rw [coordinateBlock_flatBilinear eL eR hh hr] at hp
  exact hp.trans hz

/-- Same estimate directly on the established continuity-side bilinear operator. -/
theorem gaussianBilinearOperator_paired_smallball {n h J r s d : ℕ}
    (eL eR : Fin J × Fin r ↪ Fin h) (hh : 0 < h) (hr : 0 < r) (hrs : r = 2*s)
    (u v : Fin n → ℝ) (hdisj : ∀ i, u i * v i = 0) {σ : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (hvsum : ∑ i, (v i)^2 = σ^2)
    (hvcap : ∀ i, (v i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹) :
    (tensorGaussianLaw n h).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) (u+v))) ≤
        (J:ℝ)/2 * blockThreshold σ d r} ≤
      Real.exp (-(J:ℝ)*(r:ℝ)^2/4) := by
  have hp := paired_nuclear_smallball eL eR hh hr hrs u v hdisj hσ
    (Nat.cast_pos.mpr hd) hvsum hvcap
  have heq (z : GaussianEntries n h × GaussianEntries n h) :
      flatBilinear (d:ℝ) h n (u+v) z = gaussianBilinearOperator n h d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) (u+v)) :=
    bilinearScaled_flatToSmallBall n h d hh z (MeasurableEquiv.toLp 2 (Fin n → ℝ) (u+v))
  simp_rw [heq] at hp
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hp

end GaussianPairedBlocks
