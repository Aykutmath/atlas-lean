import LateDriverGeometry

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped ENNReal
namespace GaussianPairedBlocks

/-- Restrict coefficients to the deterministic late driver. -/
def driverCoefficients {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then w i else 0

theorem driver_energy_eq {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) :
    ∑ i, (driverCoefficients S w i)^2 = ∑ i ∈ S, (w i)^2 := by
  classical
  simp [driverCoefficients]

theorem driver_mass_sq_le {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) :
    (∑ i ∈ S, |w i|)^2 ≤ (S.card:ℝ) * ∑ i, (driverCoefficients S w i)^2 := by
  rw [driver_energy_eq]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => |w i|)

theorem driver_energy_lower {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hlower : ∀ i ∈ S, ℓ ≤ |w i|) :
    (S.card:ℝ)*ℓ^2 ≤ ∑ i, (driverCoefficients S w i)^2 := by
  rw [driver_energy_eq]
  calc
    _ = ∑ _i ∈ S, ℓ^2 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => by nlinarith [hlower i hi, sq_abs (w i)]

theorem driver_coefficient_upper {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) (i : Fin n) :
    (driverCoefficients S w i)^2 ≤ 4*ℓ^2 := by
  unfold driverCoefficients
  split_ifs with hi
  · nlinarith [hupper i hi, abs_nonneg (w i), sq_abs (w i)]
  · nlinarith [sq_nonneg ℓ]

/-- Almost-constant-amplitude late drivers give the precise small-ball cap,
without restricting any coefficient outside their support. -/
theorem driver_cap {n d : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (hm : 64 ≤ min S.card d) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    ∀ i, (driverCoefficients S w i)^2 ≤
      (∑ j, (driverCoefficients S w j)^2) * (2*(lateBlockDim S.card d:ℝ))⁻¹ := by
  intro i
  obtain ⟨hh, hr, hu, hl, hJ⟩ := lateBlock_geometry hm
  have hrR : (0:ℝ) < lateBlockDim S.card d := by exact_mod_cast hr
  have h8 : 8*(lateBlockDim S.card d:ℝ) ≤ S.card := by
    have hn : 8*lateBlockDim S.card d ≤ S.card := by omega
    exact_mod_cast hn
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 2*(lateBlockDim S.card d:ℝ))]
  have hcoeff := driver_coefficient_upper S w hℓ.le hupper i
  have hlow := driver_energy_lower S w hℓ.le hlower
  have hc := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ 2*(lateBlockDim S.card d:ℝ) by positivity)
  have hl := mul_le_mul_of_nonneg_right h8 (sq_nonneg ℓ)
  nlinarith

/-- Complete macroscopic late-driver estimate under the actual Gaussian law.
Only the deterministic driver S has controlled amplitudes; all other coefficients
are arbitrary. The theorem retains the exact min(s,d)/s loss and d min(s,d) exponent. -/
theorem gaussian_late_driver_smallball_ambient {n d h : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (hm : 64 ≤ min S.card d) (hdh : d ≤ 3*h) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n h).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) * Real.sqrt d * (∑ i ∈ S, |w i|) *
          Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ≤
      Real.exp (-(d:ℝ)*(min S.card d:ℕ)/1024) := by
  let v := driverCoefficients S w
  let u := w-v
  let σ := Real.sqrt (∑ i, (v i)^2)
  have henergy : 0 < ∑ i, (v i)^2 := by
    have hs : (0:ℝ) < S.card := by exact_mod_cast (show 0<S.card by omega)
    exact lt_of_lt_of_le (mul_pos hs (sq_pos_of_pos hℓ))
      (driver_energy_lower S w hℓ.le hlower)
  have hσ : 0 < σ := Real.sqrt_pos.mpr henergy
  have hσsq : ∑ i, (v i)^2 = σ^2 := (Real.sq_sqrt henergy.le).symm
  have hdisj : ∀ i, u i*v i = 0 := by
    intro i
    dsimp [u,v,driverCoefficients]
    split_ifs <;> simp
  have huv : u+v = w := sub_add_cancel w v
  have hcap : ∀ i, (v i)^2 ≤ σ^2*(2*(lateBlockDim S.card d:ℝ))⁻¹ := by
    rw [← hσsq]
    exact driver_cap S w hm hℓ hlower hupper
  obtain ⟨hh,hr,hu,hl,hJ⟩ := lateBlock_geometry_ambient hm hdh
  have hd : 0 < d := by omega
  have hp := gaussianBilinearOperator_paired_smallball
    (consecutiveBlocks h (lateBlockDim S.card d))
    (consecutiveBlocks h (lateBlockDim S.card d))
    hh hr (show lateBlockDim S.card d = 2*(min S.card d/32) from rfl)
    u v hdisj hσ hd hσsq hcap
  rw [huv] at hp
  have hM : 0 ≤ ∑ i ∈ S, |w i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmass : (∑ i ∈ S, |w i|)^2 ≤ (S.card:ℝ)*σ^2 := by
    rw [← hσsq]
    exact driver_mass_sq_le S w
  have hthreshold := lateBlock_threshold_ambient hm hdh hM hσ hmass
  have hsub : {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
      ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
      (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)*Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ⊆
      {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
      ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
      ((h / lateBlockDim S.card d:ℕ):ℝ)/2 * blockThreshold σ d (lateBlockDim S.card d)} :=
    fun _ hz => hz.trans hthreshold
  exact ((measureReal_mono hsub).trans hp).trans (Real.exp_le_exp.mpr (by
    have := lateBlock_exponent_ambient hm hdh
    linarith))

/-- Macroscopic support specialization: the scale loses only sqrt(max(K,1)),
and the probability is exponentially small in d². -/
theorem gaussian_macroscopic_late_driver_smallball_ambient {n d h : ℕ}
    (S : Finset (Fin n)) (w : Fin n → ℝ) {c₀ K ℓ : ℝ}
    (hdh : d ≤ 3*h) (hc₀ : 0 < c₀) (hlarge : 64 ≤ min c₀ 1 * (d:ℝ))
    (hlowSize : c₀*(d:ℝ) ≤ S.card) (hupSize : (S.card:ℝ) ≤ K*(d:ℝ))
    (hℓ : 0 < ℓ) (hlower : ∀ i ∈ S, ℓ ≤ |w i|)
    (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n h).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n h d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) / Real.sqrt (max K 1) * Real.sqrt d * (∑ i ∈ S, |w i|)} ≤
      Real.exp (-(min c₀ 1)*(d:ℝ)^2/1024) := by
  have hd0 : (0:ℝ) ≤ d := by positivity
  have hmin : min c₀ 1 * (d:ℝ) ≤ (min S.card d:ℕ) := by
    rw [Nat.cast_min]
    exact le_min ((mul_le_mul_of_nonneg_right (min_le_left c₀ 1) hd0).trans hlowSize)
      (by nlinarith [mul_le_mul_of_nonneg_right (min_le_right c₀ 1) hd0])
  have hm : 64 ≤ min S.card d := by exact_mod_cast (hlarge.trans hmin)
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hs : (0:ℝ) < S.card := by exact_mod_cast (show 0<S.card by omega)
  have hK : (0:ℝ) < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hsm : (S.card:ℝ) ≤ max K 1 * (min S.card d:ℕ) := by
    rcases le_total S.card d with hsd | hds
    · rw [min_eq_left hsd]
      nlinarith [le_max_right K 1]
    · rw [min_eq_right hds]
      exact hupSize.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) hd.le)
  have hratio : 1 / max K 1 ≤ (min S.card d:ℕ)/(S.card:ℝ) := by
    rw [div_le_div_iff₀ hK hs]
    simpa [mul_comm] using hsm
  have hroot := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one] at hroot
  have hM : 0 ≤ ∑ i ∈ S, |w i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hthreshold : (1/1048576:ℝ) / Real.sqrt (max K 1) * Real.sqrt d * (∑ i ∈ S, |w i|) ≤
      (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)*Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ)) := by
    calc
      _ = ((1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|)) *
          (1 / Real.sqrt (max K 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot
        (show 0 ≤ (1/1048576:ℝ)*Real.sqrt d*(∑ i ∈ S, |w i|) by positivity)
  have hp := gaussian_late_driver_smallball_ambient S w hm hdh hℓ hlower hupper
  apply le_trans (measureReal_mono (fun z hz => hz.trans hthreshold))
    (hp.trans ?_)
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hmin hd.le
  nlinarith


theorem gaussian_late_driver_smallball {n d : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (hm : 64 ≤ min S.card d) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n (d/2)).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n (d/2) d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) * Real.sqrt d * (∑ i ∈ S, |w i|) *
          Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ≤
      Real.exp (-(d:ℝ)*(min S.card d:ℕ)/1024) :=
  gaussian_late_driver_smallball_ambient S w hm (by omega) hℓ hlower hupper

theorem gaussian_late_driver_smallball_even_half {n d : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (hm : 64 ≤ min S.card d) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, ℓ ≤ |w i|) (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n (2*(d/4))).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n (2*(d/4)) d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) * Real.sqrt d * (∑ i ∈ S, |w i|) *
          Real.sqrt ((min S.card d:ℕ)/(S.card:ℝ))} ≤
      Real.exp (-(d:ℝ)*(min S.card d:ℕ)/1024) :=
  gaussian_late_driver_smallball_ambient S w hm (by omega) hℓ hlower hupper

theorem gaussian_macroscopic_late_driver_smallball {n d : ℕ}
    (S : Finset (Fin n)) (w : Fin n → ℝ) {c₀ K ℓ : ℝ}
    (hc₀ : 0 < c₀) (hlarge : 64 ≤ min c₀ 1 * (d:ℝ))
    (hlowSize : c₀*(d:ℝ) ≤ S.card) (hupSize : (S.card:ℝ) ≤ K*(d:ℝ))
    (hℓ : 0 < ℓ) (hlower : ∀ i ∈ S, ℓ ≤ |w i|)
    (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n (d/2)).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n (d/2) d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) / Real.sqrt (max K 1) * Real.sqrt d * (∑ i ∈ S, |w i|)} ≤
      Real.exp (-(min c₀ 1)*(d:ℝ)^2/1024) := by
  have hmin : min c₀ 1 * (d:ℝ) ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right c₀ 1) (show (0:ℝ) ≤ d by positivity)]
  have hd64 : 64 ≤ d := by exact_mod_cast (hlarge.trans hmin)
  exact gaussian_macroscopic_late_driver_smallball_ambient S w (by omega) hc₀ hlarge hlowSize hupSize hℓ hlower hupper

theorem gaussian_macroscopic_late_driver_smallball_even_half {n d : ℕ}
    (S : Finset (Fin n)) (w : Fin n → ℝ) {c₀ K ℓ : ℝ}
    (hc₀ : 0 < c₀) (hlarge : 64 ≤ min c₀ 1 * (d:ℝ))
    (hlowSize : c₀*(d:ℝ) ≤ S.card) (hupSize : (S.card:ℝ) ≤ K*(d:ℝ))
    (hℓ : 0 < ℓ) (hlower : ∀ i ∈ S, ℓ ≤ |w i|)
    (hupper : ∀ i ∈ S, |w i| ≤ 2*ℓ) :
    (tensorGaussianLaw n (2*(d/4))).real
      {z | spectralNuclearNorm (gaussianBilinearOperator n (2*(d/4)) d z
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) w)) ≤
        (1/1048576:ℝ) / Real.sqrt (max K 1) * Real.sqrt d * (∑ i ∈ S, |w i|)} ≤
      Real.exp (-(min c₀ 1)*(d:ℝ)^2/1024) := by
  have hmin : min c₀ 1 * (d:ℝ) ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right c₀ 1) (show (0:ℝ) ≤ d by positivity)]
  have hd64 : 64 ≤ d := by exact_mod_cast (hlarge.trans hmin)
  exact gaussian_macroscopic_late_driver_smallball_ambient S w (by omega) hc₀ hlarge hlowSize hupSize hℓ hlower hupper

end GaussianPairedBlocks
