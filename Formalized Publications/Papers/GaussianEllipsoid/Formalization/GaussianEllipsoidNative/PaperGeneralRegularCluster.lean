import ProjectedRegularCluster

noncomputable section
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments GaussianPairedBlocks
open scoped BigOperators ENNReal
namespace GaussianEllipsoid.ProjectedClusters

def regularScale (C : ℝ) : ℝ := 16/(16+C)
def generalLow (C : ℝ) : ℝ := 8192/(regularScale C)^2
def generalUp (c C : ℝ) : ℝ := 4*c/(regularScale C)^2
def generalProj (c C : ℝ) : ℝ :=
  min (4*c*regularScale C*projectedConstant) (4*c*(regularScale C)^2/65536)

theorem regularScale_pos {C : ℝ} (hC : 0 < C) : 0 < regularScale C := by unfold regularScale; positivity

theorem generalConstants_pos {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    0 < generalLow C ∧ 0 < generalUp c C ∧ 0 < generalProj c C := by
  have hk := regularScale_pos hC
  have hp := projectedConstant_pos
  unfold generalLow generalUp generalProj
  refine ⟨by positivity, by positivity, by positivity⟩

lemma blockThreshold_rescale {σ D d : ℝ} (hD : 0 < D) (hd : 0 < d) (r : ℕ) :
    blockThreshold σ D r * (Real.sqrt D / Real.sqrt d) = blockThreshold σ d r := by
  unfold blockThreshold
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hD),ne_of_gt (Real.sqrt_pos.mpr hd)]

/-- General-rank, general-regularity fixed-projection form of the paper's regular-group lemma.
The constants are selected solely from c_rank and C_reg, before all dimensions and coefficients. -/
theorem projected_regular_cluster_general {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    {n h d : ℕ} (hd2 : 2 ≤ d)
    (W Z : Submodule ℝ (Euclid h))
    (hW : c*(d:ℝ) ≤ finrank ℝ W) (hZ : c*(d:ℝ) ≤ finrank ℝ Z)
    (u : Euclid n) {σ m R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hm : m = ∑ i, |u i|)
    (hRdef : R = m^2/σ^2)
    (hlow : generalLow C * Real.log (d:ℝ) ≤ R)
    (hupp : R ≤ generalUp c C * (d:ℝ))
    (hcap : ∀ i, |u i| ≤ C*σ/Real.sqrt R) :
    tensorGaussianLaw n h
      {z | spectralNuclearNorm (projectedBilinear (W.subtypeL ∘L W.orthogonalProjection)
        (Z.subtypeL ∘L Z.orthogonalProjection) n d z u) <
        generalProj c C * Real.sqrt d * m} ≤
      ENNReal.ofReal (Real.exp (-generalProj c C * (d:ℝ) * R)) := by
  let κ := regularScale C
  let Rt := κ^2*R
  let D := 4*c*(d:ℝ)
  let k := min (finrank ℝ W) (finrank ℝ Z)
  let r := regularBlockSize Rt
  let J := k/r
  have hκ : 0 < κ := regularScale_pos hC
  have hκsq : κ^2 ≠ 0 := pow_ne_zero 2 hκ.ne'
  have hd : 0 < d := by omega
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hD : 0 < D := by dsimp [D]; positivity
  have hRt : 4096 ≤ Rt := by
    apply regularCluster_log_cutoff hd2
    have hh := mul_le_mul_of_nonneg_left hlow (sq_nonneg κ)
    change κ^2*((8192/κ^2)*Real.log (d:ℝ)) ≤ Rt at hh
    have he : κ^2*((8192/κ^2)*Real.log (d:ℝ)) = 8192*Real.log (d:ℝ) := by field_simp
    rwa [he] at hh
  have hRtD : Rt ≤ D := by
    have hh := mul_le_mul_of_nonneg_left hupp (sq_nonneg κ)
    change Rt ≤ κ^2*((4*c/κ^2)*(d:ℝ)) at hh
    have he : κ^2*((4*c/κ^2)*(d:ℝ)) = D := by dsimp [D]; field_simp
    rwa [he] at hh
  have hR0 : 0 < R := by
    have hp : 0 < Rt/κ^2 := div_pos (by linarith) (sq_pos_of_pos hκ)
    have he : Rt/κ^2 = R := by dsimp [Rt]; field_simp
    rwa [he] at hp
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hsd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdR
  have hroot : Real.sqrt Rt = κ*Real.sqrt R := by
    dsimp [Rt]
    rw [Real.sqrt_mul (sq_nonneg κ),Real.sqrt_sq hκ.le]
  have hmass : 0 ≤ m := by rw [hm]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hms : m = σ*Real.sqrt R := by
    apply (sq_eq_sq₀ hmass (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hR0.le,hRdef]
    field_simp
  have hκC : κ*C ≤ 16 := by
    have he : κ*(16+C)=16 := by dsimp [κ,regularScale]; field_simp
    nlinarith
  have hcap' (i : Fin n) : |u i| ≤ 16*σ/Real.sqrt Rt := by
    rw [hroot]
    apply (le_div_iff₀ (mul_pos hκ hsR)).mpr
    calc
      _ = κ*(|u i| * Real.sqrt R) := by ring
      _ ≤ κ*(C*σ) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hsR).mp (hcap i)) hκ.le
      _ ≤ 16*σ := by nlinarith [mul_le_mul_of_nonneg_right hκC hσ.le]
  have hk : D/4 ≤ k := by
    have hh : c*(d:ℝ) ≤ k := by
      dsimp [k]
      rw [Nat.cast_min]
      exact le_min hW hZ
    dsimp [D]
    nlinarith
  have hk0 : 0 < k := by
    have hp : (0:ℝ)<k := lt_of_lt_of_le (by positivity : 0 < D/4) hk
    exact_mod_cast hp
  have hr := regularBlockSize_bounds hRt
  have hr0 : 0 < r := by dsimp [r]; omega
  have hb := projected_nuclear_paired_smallball W Z (Nat.min_le_left _ _) (Nat.min_le_right _ _)
    hk0 hr0 (show r = 2*regularBlockHalf Rt from rfl) u hσ hd husum
    (fun i => regularBlock_coefficient_cap hRt hσ (hcap' i))
  have hmt : κ*m = σ*Real.sqrt Rt := by rw [hms,hroot]; ring
  have ht := regularBlock_threshold hRt hRtD hk hσ hmt
  change projectedConstant * Real.sqrt D * (κ*m) ≤ (J:ℝ)/2*blockThreshold σ D r at ht
  have ht' := mul_le_mul_of_nonneg_right ht (div_nonneg hsD.le hsd.le)
  have hleft : (projectedConstant * Real.sqrt D * (κ*m))*(Real.sqrt D/Real.sqrt (d:ℝ)) =
      (4*c*κ*projectedConstant)*Real.sqrt d*m := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hsd.ne').mpr
    ring_nf
    rw [Real.sq_sqrt hD.le,Real.sq_sqrt hdR.le]
    dsimp [D]
    ring
  have hright : ((J:ℝ)/2*blockThreshold σ D r)*(Real.sqrt D/Real.sqrt (d:ℝ)) =
      (J:ℝ)/2*blockThreshold σ d r := by rw [mul_assoc,blockThreshold_rescale hD hdR]
  rw [hleft,hright] at ht'
  have hmin : generalProj c C ≤ 4*c*κ*projectedConstant := min_le_left _ _
  have htfinal : generalProj c C*Real.sqrt d*m ≤ (J:ℝ)/2*blockThreshold σ d r := by
    have hp := mul_le_mul_of_nonneg_right hmin (mul_nonneg hsd.le hmass)
    apply le_trans _ ht'
    simpa only [mul_assoc] using hp
  have he := regularBlock_exponent hRt hRtD hk
  have hrate : generalProj c C ≤ 4*c*κ^2/65536 := min_le_right _ _
  have hrate' : generalProj c C*(d:ℝ)*R ≤ D*Rt/65536 := by
    have hh := mul_le_mul_of_nonneg_right hrate (mul_nonneg hdR.le hR0.le)
    dsimp only [D,Rt]
    nlinarith [hh]
  apply (measure_mono ?_).trans (hb.trans ?_)
  · intro z hz
    exact hz.le.trans htfinal
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change -(J:ℝ)*(r:ℝ)^2/4 ≤ -generalProj c C*(d:ℝ)*R
    linarith

#print axioms generalConstants_pos
#print axioms projected_regular_cluster_general
end GaussianEllipsoid.ProjectedClusters
