/-
DSClassical (direct classical Davidson–Szarek covariance bound (net + self-bounding).

Route (Davidson–Szarek 2001, Theorem II.13, net + self-bounding argument):
1. Per-center: for fixed in-ball `v`, the two-sided tail
   `|quadratic (Σ̂ - I) v|` comes from `dsPerCenterTail`, taken as an
   EXPLICIT hypothesis `hpc` throughout (proved in a parallel lane; never
   assumed globally). The two-sided form covers both tails (`+quadratic`
   and `-quadratic`, i.e. lamMax and -lamMin) in one shot with budget
   `2 * exp(-x)`.
2. Net: an eps-net of the unit ball from `dsNetCard_of_volnets` (DSNet,
   discharging `dsNetCard` via VolNets; no net premise is assumed) plus
   the union bound `prob_iUnion_le_card_smul` (UnionNet).
3. Self-bounding transfer: `dsClassQuadTransfer` (pure algebra, proved
   here) bounds `|quadratic A u|` by the net-center value plus
   `(2*eps) * matrixOpNorm A`; the `(2*eps+eps^2)` form
   (`dsClassQuadTransfer_rho`) and the abstract solve step
   (`dsClassSolve`) are also proved. The ball-sup + solve assembly is
   imported as `opNorm_le_net_max_quadratic` (Discretize), whose proof
   instantiates exactly this pattern (its Step 1 proves the `M ≤ Q`
   link via polarization, which is not re-proved here).
4. Parameters `(eps, x) = (1/15, 4d)`: card `(1+2/eps)^d = 31^d`,
   transfer factor `1/(1-2*eps-eps^2) = 225/194`, per-center threshold
   `2√(4d/n) + 8(d/n) = 4√(d/n) + 8(d/n)`, budget
   `31^d * 2e^{-4d} ≤ 2e^{-d/2}` (`dsClassEndgame`, needs
   `31 ≤ e^{7/2}`, proved as `31 ≤ 31.8440176 ≤ e^3 * e^{1/2}`).
   Final: threshold `(450/97)√(d/n) + (900/97)(d/n) ≈ 4.64√(d/n) +
   9.28(d/n)` with the FULL budget `2 * exp(-d/2)`
   (`dsClassicalCovariance`).

On (4,4): `dsClassThreshold_gt_var` proves the classical threshold
strictly exceeds the (4,4) threshold, so the proved bound does not imply
`davidsonSzarekCovariance` by monotonicity. The blocking arithmetic step
is isolated as `dsClassFit` (classical threshold ≤ (4,4) threshold):
`ds44_of_classical_of_fit` derives the exact target from the classical
bound plus the fit, and `dsClassFit_false` proves the fit is false.
Per the parallel DSVAR lane (`/tmp/g_dsvar/DSVAR.md` §3), no `(eps, x)`
re-tuning within the net route closes both the threshold gap and the
budget gap jointly (counting needs `x/d ≥ 1/2 + log(1+2/eps)` while the
(4,4) fit allows less — a monotone fixpoint contradiction in `eps`);
closing (4,4) needs input from outside this route.
-/

import GaussianEllipsoid.DSCovariance
import GaussianEllipsoid.DSNet
import GaussianEllipsoid.Discretize
import GaussianEllipsoid.UnionNet

set_option autoImplicit false

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

/-! ## 1. Self-bounding transfer algebra (pure, no probability) -/

/-- Pointwise self-bounding transfer (pure algebra): for an in-ball net
center `v` within `eps` of an in-ball `u`, the quadratic value at `u` is
controlled by the value at `v` plus `(2*eps)` times the operator norm.
No symmetry is needed: the two cross terms are bounded by Cauchy–Schwarz
plus the operator-norm action bound. -/
theorem dsClassQuadTransfer {d : Nat} {A : Square d}
    {u v : Vector d} {eps : ℝ} (hu : euclidNorm u ≤ 1)
    (hv : euclidNorm v ≤ 1) (he : euclidNorm (u - v) ≤ eps)
    (heps0 : 0 ≤ eps) :
    |quadratic A u| ≤ |quadratic A v| + (2 * eps) * matrixOpNorm A := by
  have hdiff : quadratic A u - quadratic A v
      = (u - v) ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ (u - v)) := by
    have hdecomp : u = v + (u - v) := by abel
    conv_lhs => rw [hdecomp]
    unfold quadratic
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
      dotProduct_add, dotProduct_sub]
    ring
  have hMnn : (0 : ℝ) ≤ matrixOpNorm A := matrixOpNorm_nonneg A
  have hAu : euclidNorm (A *ᵥ u) ≤ matrixOpNorm A * euclidNorm u :=
    matrixOpNorm_mulVec_le A u
  have hAe : euclidNorm (A *ᵥ (u - v))
      ≤ matrixOpNorm A * euclidNorm (u - v) :=
    matrixOpNorm_mulVec_le A (u - v)
  have hcs1 := dotProduct_abs_le_euclidNorm (u - v) (A *ᵥ u)
  have hcs2 := dotProduct_abs_le_euclidNorm v (A *ᵥ (u - v))
  have hAu1 : euclidNorm (A *ᵥ u) ≤ matrixOpNorm A * 1 :=
    hAu.trans (mul_le_mul_of_nonneg_left hu hMnn)
  have hb1 : |(u - v) ⬝ᵥ (A *ᵥ u)| ≤ eps * matrixOpNorm A := by
    calc |(u - v) ⬝ᵥ (A *ᵥ u)|
        ≤ euclidNorm (u - v) * euclidNorm (A *ᵥ u) := hcs1
      _ ≤ eps * euclidNorm (A *ᵥ u) :=
          mul_le_mul_of_nonneg_right he (euclidNorm_nonneg _)
      _ ≤ eps * (matrixOpNorm A * 1) :=
          mul_le_mul_of_nonneg_left hAu1 heps0
      _ = eps * matrixOpNorm A := by ring
  have hAe1 : euclidNorm (A *ᵥ (u - v)) ≤ matrixOpNorm A * eps :=
    hAe.trans (mul_le_mul_of_nonneg_left he hMnn)
  have hb2 : |v ⬝ᵥ (A *ᵥ (u - v))| ≤ eps * matrixOpNorm A := by
    calc |v ⬝ᵥ (A *ᵥ (u - v))|
        ≤ euclidNorm v * euclidNorm (A *ᵥ (u - v)) := hcs2
      _ ≤ 1 * euclidNorm (A *ᵥ (u - v)) :=
          mul_le_mul_of_nonneg_right hv (euclidNorm_nonneg _)
      _ ≤ 1 * (matrixOpNorm A * eps) :=
          mul_le_mul_of_nonneg_left hAe1 zero_le_one
      _ = eps * matrixOpNorm A := by ring
  have hbound : |quadratic A u - quadratic A v|
      ≤ (2 * eps) * matrixOpNorm A := by
    rw [hdiff]
    calc |(u - v) ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ (u - v))|
        ≤ |(u - v) ⬝ᵥ (A *ᵥ u)| + |v ⬝ᵥ (A *ᵥ (u - v))| :=
          abs_add_le _ _
      _ ≤ eps * matrixOpNorm A + eps * matrixOpNorm A :=
          add_le_add hb1 hb2
      _ = (2 * eps) * matrixOpNorm A := by ring
  have htri : |quadratic A u| ≤ |quadratic A v|
      + |quadratic A u - quadratic A v| := by
    have h := abs_sub_abs_le_abs_sub (quadratic A u) (quadratic A v)
    linarith
  linarith [htri, hbound]

/-- The `(2*eps + eps^2)` form of the transfer: the in-ball `2*eps`
bound implies the radius-transfer form used below. -/
theorem dsClassQuadTransfer_rho {d : Nat} {A : Square d}
    {u v : Vector d} {eps : ℝ} (hu : euclidNorm u ≤ 1)
    (hv : euclidNorm v ≤ 1) (he : euclidNorm (u - v) ≤ eps)
    (heps0 : 0 ≤ eps) :
    |quadratic A u|
      ≤ |quadratic A v| + (2 * eps + eps ^ 2) * matrixOpNorm A := by
  have h := dsClassQuadTransfer (A := A) hu hv he heps0
  have hnn : (0 : ℝ) ≤ eps ^ 2 * matrixOpNorm A :=
    mul_nonneg (sq_nonneg _) (matrixOpNorm_nonneg A)
  have e : (2 * eps + eps ^ 2) * matrixOpNorm A
      = (2 * eps) * matrixOpNorm A + eps ^ 2 * matrixOpNorm A := by ring
  linarith [h, hnn, e]

/-- Abstract self-bounding solve step: from `M ≤ Q ≤ t + δ*M` with
`δ < 1`, conclude `M ≤ t / (1-δ)`. The hypotheses are discharged inside
`opNorm_le_net_max_quadratic` (Discretize: `M ≤ Q` by polarization,
`Q ≤ t + δ*M` from the pointwise transfer maximized over the net). -/
theorem dsClassSolve {M Q t δ : ℝ} (hδ : δ < 1)
    (hM : M ≤ Q) (hQ : Q ≤ t + δ * M) : M ≤ t / (1 - δ) := by
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  rw [le_div_iff₀ hpos]
  have e : M * (1 - δ) = M - δ * M := by ring
  linarith [hM, hQ, e]

/-! ## 2. Exponential endgame at `(N₁, c) = (31, 4)` -/

/-- `31 ≤ e^{7/2} = e^3 * e^{1/2}`, from `2.71 ≤ e` and
`1.6 ≤ e^{1/2}` (`2.71^3 * 1.6 = 31.8440176`). -/
theorem dsClassThirtyOne_le_exp72 : (31 : ℝ) ≤ Real.exp (7 / 2) := by
  have h1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 := dsExpHalf_ge
  have h2nn : (0 : ℝ) ≤ (2.71 : ℝ) := by norm_num
  have h3 : (2.71 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
    pow_le_pow_left₀ h2nn h1 3
  have he1nn : (0 : ℝ) ≤ Real.exp 1 := Real.exp_nonneg _
  have h4 : (2.71 : ℝ) ^ 3 * 1.6 ≤ (Real.exp 1) ^ 3 * Real.exp (1 / 2) :=
    mul_le_mul h3 h2 (by norm_num) (pow_nonneg he1nn 3)
  have hex72 : (7 / 2 : ℝ) = 1 + 1 + 1 + 1 / 2 := by norm_num
  rw [hex72, Real.exp_add, Real.exp_add, Real.exp_add]
  have hconst : (2.71 : ℝ) ^ 3 * 1.6 = 31.8440176 := by norm_num
  have h5 : (31.8440176 : ℝ) ≤ (Real.exp 1) ^ 3 * Real.exp (1 / 2) := by
    rw [← hconst]
    exact h4
  have h6 : ((Real.exp 1 * Real.exp 1) * Real.exp 1) * Real.exp (1 / 2)
      = (Real.exp 1) ^ 3 * Real.exp (1 / 2) := by ring
  rw [h6]
  linarith [h5]

/-- Union-bound endgame: `31^d * 2e^{-4d} ≤ 2e^{-d/2}`, by induction. -/
theorem dsClassEndgame (d : ℕ) :
    (31 : ℝ) ^ d * (2 * Real.exp (-(4 * (d : ℝ))))
      ≤ 2 * Real.exp (-(d : ℝ) / 2) := by
  induction d with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, mul_zero, neg_zero, zero_div,
        Real.exp_zero, mul_one, one_mul]
      exact le_rfl
  | succ d ih =>
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
      have hexp4 : (-(4 * ((d : ℝ) + 1))) = (-(4 * (d : ℝ))) + (-4) := by ring
      have hexpH : (-((d : ℝ) + 1) / 2) = (-(d : ℝ) / 2) + (-(1 / 2)) := by
        ring
      have hLHS : (31 : ℝ) ^ (d + 1) * (2 * Real.exp (-(4 * ((d : ℝ) + 1))))
          = (31 * Real.exp (-4))
            * ((31 : ℝ) ^ d * (2 * Real.exp (-(4 * (d : ℝ))))) := by
        rw [pow_succ, hexp4, Real.exp_add]; ring
      have hRHS : Real.exp (-(1 / 2 : ℝ)) * (2 * Real.exp (-(d : ℝ) / 2))
          = 2 * Real.exp (-((d : ℝ) + 1) / 2) := by
        rw [hexpH, Real.exp_add]; ring
      have h31e : (31 : ℝ) * Real.exp (-4) ≤ Real.exp (-(1 / 2 : ℝ)) := by
        have h72 : ((7 / 2 : ℝ)) + (-4) = -(1 / 2) := by norm_num
        calc (31 : ℝ) * Real.exp (-4)
            ≤ Real.exp (7 / 2) * Real.exp (-4) :=
              mul_le_mul_of_nonneg_right dsClassThirtyOne_le_exp72
                (Real.exp_nonneg _)
          _ = Real.exp (-(1 / 2 : ℝ)) := by rw [← Real.exp_add, h72]
      have hnn1 : (0 : ℝ) ≤ 31 * Real.exp (-4) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      have hnn2 : (0 : ℝ) ≤ 2 * Real.exp (-(d : ℝ) / 2) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      rw [hcast, hLHS]
      calc (31 * Real.exp (-4))
              * ((31 : ℝ) ^ d * (2 * Real.exp (-(4 * (d : ℝ)))))
          ≤ (31 * Real.exp (-4)) * (2 * Real.exp (-(d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left ih hnn1
        _ ≤ Real.exp (-(1 / 2 : ℝ)) * (2 * Real.exp (-(d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right h31e hnn2
        _ = 2 * Real.exp (-((d : ℝ) + 1) / 2) := hRHS

/-! ## 3. Thresholds at `(eps, x) = (1/15, 4d)` -/

/-- Per-center threshold at `x = 4d`. -/
def dsClassPerCenterT (d n : Nat) : ℝ :=
  2 * Real.sqrt ((4 * (d : ℝ)) / (n : ℝ)) + 2 * (4 * (d : ℝ)) / (n : ℝ)

/-- Classical-route threshold at `eps = 1/15` (transfer factor `225/194`). -/
def dsClassThreshold (d n : Nat) : ℝ := dsClassPerCenterT d n * (225 / 194)

/-- `(194/225)·T = t_c`: the transfer factor cancels by construction. -/
theorem dsClassRhoT_eq (d n : Nat) :
    (194 / 225 : ℝ) * dsClassThreshold d n = dsClassPerCenterT d n := by
  unfold dsClassThreshold
  ring

/-- Closed form: `T_class = (450/97)√(d/n) + (900/97)(d/n)`. -/
theorem dsClassThreshold_eq (d n : Nat) :
    dsClassThreshold d n
      = (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
        + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ) := by
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq h2nn]
  have h4nn : (0 : ℝ) ≤ 4 := by norm_num
  have hsq : Real.sqrt ((4 * (d : ℝ)) / (n : ℝ))
      = 2 * Real.sqrt ((d : ℝ) / (n : ℝ)) := by
    have e : ((4 * (d : ℝ)) / (n : ℝ)) = 4 * ((d : ℝ) / (n : ℝ)) := by ring
    rw [e, Real.sqrt_mul h4nn, h4]
  have elin : 2 * (4 * (d : ℝ)) / (n : ℝ) = 8 * ((d : ℝ) / (n : ℝ)) := by ring
  unfold dsClassThreshold dsClassPerCenterT
  rw [hsq, elin]
  ring

/-! ## 4. Main assembly -/

theorem dsClassicalCovarianceNet (hpc : dsPerCenterTail) :
    ∀ (d n : Nat), 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
      ((gaussianSampleLaw d n)
        {x | dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
        ≤ 2 * Real.exp (-(d : ℝ) / 2) := by
  intro d n hd hn hdn
  obtain ⟨N, v, hcard, hinball, hnet⟩ :=
    dsNetCard_of_volnets d (show (0 : ℝ) < (1 / 15 : ℝ) by norm_num)
  have h31 : (1 : ℝ) + 2 / (1 / 15 : ℝ) = 31 := by norm_num
  rw [h31] at hcard
  have h31ceil : Nat.ceil ((31 : ℝ) ^ d) = (31 : ℝ) ^ d := by
    have hnat : (31 : ℝ) ^ d = ((31 ^ d : ℕ) : ℝ) := by norm_cast
    rw [hnat, Nat.ceil_natCast]
  rw [h31ceil] at hcard
  have heps0 : (0 : ℝ) ≤ (1 / 15 : ℝ) := by norm_num
  have heps1 : 2 * (1 / 15 : ℝ) + (1 / 15 : ℝ) ^ 2 < 1 := by norm_num
  have hρ : (1 : ℝ) - 2 * (1 / 15 : ℝ) - (1 / 15 : ℝ) ^ 2 = 194 / 225 := by
    norm_num
  have hper : ∀ k : Fin N,
      (gaussianSampleLaw d n)
          {z | dsClassPerCenterT d n
            < |quadratic (sampleCovariance z - 1) (v k)|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ)))) := by
    intro k
    exact dsPerCenter_inball hpc hn (hinball k)
      (show (0 : ℝ) ≤ 4 * (d : ℝ) by positivity)
      (by unfold dsClassPerCenterT; exact le_rfl)
  have hsymm : ∀ x : Sample d n, (sampleCovariance x - 1).IsSymm :=
    fun x => sampleCovariance_sub_one_symm_ds x
  have hsub : {x : Sample d n |
        dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}
      ⊆ ⋃ k : Fin N,
        {z : Sample d n |
          dsClassPerCenterT d n
            < |quadratic (sampleCovariance z - 1) (v k)|} := by
    intro x hx
    obtain ⟨k, hk⟩ := opNorm_le_net_max_quadratic (hsymm x) heps0 heps1 hnet
    rw [hρ] at hk
    have hlt : dsClassThreshold d n
        < |quadratic (sampleCovariance x - 1) (v k)| / (194 / 225) :=
      lt_of_lt_of_le hx hk
    have hmul := mul_lt_mul_of_pos_right hlt (by norm_num : (0 : ℝ) < 194 / 225)
    have heq : (|quadratic (sampleCovariance x - 1) (v k)| / (194 / 225 : ℝ))
          * (194 / 225)
        = |quadratic (sampleCovariance x - 1) (v k)| := by
      rw [div_eq_mul_inv, mul_assoc,
        inv_mul_cancel₀ (by norm_num : (194 / 225 : ℝ) ≠ 0), mul_one]
    have hρT := dsClassRhoT_eq d n
    have hmem : dsClassPerCenterT d n
        < |quadratic (sampleCovariance x - 1) (v k)| := by
      have hcomm : dsClassThreshold d n * (194 / 225)
          = (194 / 225) * dsClassThreshold d n := mul_comm _ _
      linarith [hmul, heq, hρT, hcomm]
    exact Set.mem_iUnion.mpr ⟨k, hmem⟩
  have hU := prob_iUnion_le_card_smul (gaussianSampleLaw d n)
    (fun k : Fin N => {z : Sample d n |
      dsClassPerCenterT d n < |quadratic (sampleCovariance z - 1) (v k)|})
    (fun k => hper k)
  have hle : (gaussianSampleLaw d n)
        {x : Sample d n |
          dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}
      ≤ (N : ℕ) • ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ)))) :=
    (measure_mono hsub).trans hU
  have hsum : (∑ _k ∈ (Finset.univ : Finset (Fin N)),
        ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ)))))
      = (N : ℕ) • ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ)))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← hsum] at hle
  have hbdd : (0 : ℝ) ≤ 2 * Real.exp (-(4 * (d : ℝ))) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hfin : (∑ _k ∈ (Finset.univ : Finset (Fin N)),
        ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ))))) ≠ ∞ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hbdd)]
    exact ENNReal.ofReal_ne_top
  have htoReal : ((gaussianSampleLaw d n)
        {x : Sample d n |
          dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ (N : ℝ) * (2 * Real.exp (-(4 * (d : ℝ)))) := by
    calc ((gaussianSampleLaw d n)
            {x : Sample d n |
              dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
        ≤ (∑ _k ∈ (Finset.univ : Finset (Fin N)),
            ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ))))).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = ∑ _k ∈ (Finset.univ : Finset (Fin N)),
          (ENNReal.ofReal (2 * Real.exp (-(4 * (d : ℝ))))).toReal :=
          ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)
      _ = ∑ _k ∈ (Finset.univ : Finset (Fin N)),
          (2 * Real.exp (-(4 * (d : ℝ)))) :=
          Finset.sum_congr rfl fun _ _ => ENNReal.toReal_ofReal hbdd
      _ = (N : ℝ) * (2 * Real.exp (-(4 * (d : ℝ)))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ((gaussianSampleLaw d n)
          {x : Sample d n |
            dsClassThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ (N : ℝ) * (2 * Real.exp (-(4 * (d : ℝ)))) := htoReal
    _ ≤ (31 : ℝ) ^ d * (2 * Real.exp (-(4 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard hbdd
    _ ≤ 2 * Real.exp (-(d : ℝ) / 2) := dsClassEndgame d

/-- Classical net-route covariance bound at `(eps, x) = (1/15, 4d)`:
threshold `(450/97)√(d/n) + (900/97)(d/n)` with the full `2e^{-d/2}`
budget. Takes only `dsPerCenterTail` as a hypothesis. -/
theorem dsClassicalCovariance (hpc : dsPerCenterTail) :
    ∀ (d n : Nat), 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
      ((gaussianSampleLaw d n)
        {x | (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
            + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ)
          < matrixOpNorm (sampleCovariance x - 1)}).toReal
        ≤ 2 * Real.exp (-(d : ℝ) / 2) := by
  intro d n hd hn hdn
  have hmain := dsClassicalCovarianceNet hpc d n hd hn hdn
  rw [dsClassThreshold_eq d n] at hmain
  exact hmain

/-! ## 5. Gap to (4,4): the blocking step, isolated and refuted -/

/-- The classical threshold strictly exceeds the (4,4) threshold. -/
theorem dsClassThreshold_gt_var (d n : Nat) (hd : 0 < d) (hn : 0 < n) :
    4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
      < (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
        + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : (0 : ℝ) < Real.sqrt ((d : ℝ) / (n : ℝ)) :=
    Real.sqrt_pos.mpr (div_pos hdR hnR)
  have hr : (0 : ℝ) ≤ (d : ℝ) / (n : ℝ) := div_nonneg hdR.le hnR.le
  have h1 : 4 * Real.sqrt ((d : ℝ) / (n : ℝ))
      < (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ)) :=
    mul_lt_mul_of_pos_right (by norm_num : (4 : ℝ) < 450 / 97) hs
  have h2 : (4 : ℝ) * ((d : ℝ) / (n : ℝ))
      ≤ (900 / 97 : ℝ) * ((d : ℝ) / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 900 / 97) hr
  have e1 : (4 : ℝ) * (d : ℝ) / (n : ℝ) = 4 * ((d : ℝ) / (n : ℝ)) := by ring
  have e2 : (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ)
      = (900 / 97 : ℝ) * ((d : ℝ) / (n : ℝ)) := by ring
  rw [e1, e2]
  linarith [h1, h2]

/-- The blocking arithmetic step, isolated: the classical threshold would
have to fit under the (4,4) threshold. -/
def dsClassFit : Prop :=
  ∀ d n : Nat, (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
      + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ)
    ≤ 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)

/-- The exact (4,4) bound follows from the classical bound plus the fit. -/
theorem ds44_of_classical_of_fit (hpc : dsPerCenterTail) (hfit : dsClassFit) :
    davidsonSzarekCovariance := by
  unfold davidsonSzarekCovariance
  intro d n hd hn hdn
  have hmain := dsClassicalCovariance hpc d n hd hn hdn
  have hsub : {x : Sample d n |
        4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
          < matrixOpNorm (sampleCovariance x - 1)}
      ⊆ {x : Sample d n |
        (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
            + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ)
          < matrixOpNorm (sampleCovariance x - 1)} := by
    intro x hx
    exact lt_of_le_of_lt (hfit d n) hx
  calc ((gaussianSampleLaw d n)
          {x : Sample d n |
            4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
              < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ ((gaussianSampleLaw d n)
          {x : Sample d n |
            (450 / 97 : ℝ) * Real.sqrt ((d : ℝ) / (n : ℝ))
                + (900 / 97 : ℝ) * (d : ℝ) / (n : ℝ)
              < matrixOpNorm (sampleCovariance x - 1)}).toReal :=
        ENNReal.toReal_mono (sampleLaw_ne_top _) (measure_mono hsub)
    _ ≤ 2 * Real.exp (-(d : ℝ) / 2) := hmain

/-- The fit is false: the classical threshold exceeds (4,4) already at
`d = n = 1`. So `dsClassFit` is the precise false arithmetic step
blocking (4,4) on this route. -/
theorem dsClassFit_false : ¬ dsClassFit := by
  intro hfit
  have h := hfit 1 1
  have g := dsClassThreshold_gt_var 1 1 (by norm_num) (by norm_num)
  linarith [h, g]

/-! ## 6. (A,B) generalization (downstream threading)

The exact `(4,4)` premise is unreachable on the net route
(`dsClassFit_false`, DSVAR fixpoint obstruction), but every downstream
consumer (deleted-covariance union bound, `covC` threshold assembly, Huber
residuals) is constant-agnostic: it needs *some* `(A, B)` with `0 < A`,
`0 ≤ B`, the same budget `2e^{-d/2}`, and the same `A√(d/n) + B(d/n)`
shape. This section states that generalized premise and proves the
`(450/97, 900/97)` instance proved above. -/

/-- The (A,B)-generalized Davidson–Szarek covariance premise: threshold
`A√(d/n) + B(d/n)` with the same budget `2e^{-d/2}`. The `(4,4)` premise
`davidsonSzarekCovariance` is the special case `A = B = 4`. -/
def davidsonSzarekCovariance_gen (A B : ℝ) : Prop :=
  ∀ d n : Nat, 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
    ((gaussianSampleLaw d n)
      {x | A * Real.sqrt ((d : ℝ) / (n : ℝ)) + B * (d : ℝ) / (n : ℝ)
        < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2)

/-- The classical bound is the `(450/97, 900/97)` instance of the
generalized premise. -/
theorem dsClassicalCovariance_gen (hpc : dsPerCenterTail) :
    davidsonSzarekCovariance_gen (450 / 97) (900 / 97) := by
  intro d n hd hn hdn
  exact dsClassicalCovariance hpc d n hd hn hdn

/-- Positivity side conditions for the classical constants. -/
theorem dsClassicalAB_pos : (0 : ℝ) < 450 / 97 ∧ (0 : ℝ) ≤ 900 / 97 := by
  constructor <;> norm_num


end GaussianEllipsoid
