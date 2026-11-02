import ClippedL1Bridge
import BMFiniteGibbsHessian

/-!
# The fixed rational residual loss as genuine bounded C² Gibbs data

The potential is exactly `(t - 1)^2 / (1 + (t - 1)^2)`.  All derivatives,
continuity certificates, and global bounds are proved here, rather than supplied
as hypotheses.  The existing clipping bridge is reused through `smoothLoss`.
-/

noncomputable section
open scoped BigOperators BoundedContinuousFunction
open BMClippedL1Bridge

namespace BMRationalLossData

/-- The unshifted first derivative, in the formula already proved by the bridge. -/
def first (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2) ^ 2

/-- The explicit unshifted second derivative. -/
def second (t : ℝ) : ℝ := (2 - 6 * t ^ 2) / (1 + t ^ 2) ^ 3

lemma first_eq_deriv (t : ℝ) : first t = deriv smoothLoss t :=
  (smoothLoss_deriv t).symm

lemma smoothLoss_hasDerivAt_first (t : ℝ) : HasDerivAt smoothLoss (first t) t :=
  smoothLoss_hasDerivAt t

lemma first_hasDerivAt_second (t : ℝ) : HasDerivAt first (second t) t := by
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_id t).const_mul 2).div
    (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).pow 2)
    (pow_ne_zero 2 hden)
  convert! h using 1
  dsimp [second]
  field_simp
  ring

lemma second_eq_deriv_first (t : ℝ) : second t = deriv first t :=
  (first_hasDerivAt_second t).deriv.symm

lemma first_abs_le_one (t : ℝ) : |first t| ≤ 1 := by
  rw [first_eq_deriv]
  exact smoothLoss_abs_deriv_le_one t

/-- A sharp global bound sufficient for the Gibbs Hessian estimates. -/
lemma second_abs_le_two (t : ℝ) : |second t| ≤ 2 := by
  have hden : (0 : ℝ) < (1 + t ^ 2) ^ 3 := by positivity
  have h4 : 0 ≤ (t ^ 2) ^ 2 := sq_nonneg _
  have h6 : 0 ≤ (t ^ 2) ^ 3 := by positivity
  unfold second
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

lemma first_continuous : Continuous first := by
  unfold first
  fun_prop (disch := intro x; positivity)

lemma second_continuous : Continuous second := by
  unfold second
  fun_prop (disch := intro x; positivity)

/-- The residual potential is the exact loss used by the bounded-risk/L1 bridge. -/
def shifted (t : ℝ) : ℝ := smoothLoss (t - 1)

def shiftedFirst (t : ℝ) : ℝ := first (t - 1)

def shiftedSecond (t : ℝ) : ℝ := second (t - 1)

@[simp] lemma shifted_formula (t : ℝ) :
    shifted t = (t - 1) ^ 2 / (1 + (t - 1) ^ 2) := rfl

@[simp] lemma shiftedFirst_formula (t : ℝ) :
    shiftedFirst t = 2 * (t - 1) / (1 + (t - 1) ^ 2) ^ 2 := rfl

@[simp] lemma shiftedSecond_formula (t : ℝ) :
    shiftedSecond t = (2 - 6 * (t - 1) ^ 2) / (1 + (t - 1) ^ 2) ^ 3 := rfl

lemma shifted_contDiff : ContDiff ℝ ⊤ shifted :=
  smoothLoss_contDiff.comp (contDiff_id.sub contDiff_const)

lemma shifted_hasDerivAt (t : ℝ) : HasDerivAt shifted (shiftedFirst t) t := by
  simpa only [Function.comp_def, mul_one] using!
    (smoothLoss_hasDerivAt_first (t - 1)).comp t ((hasDerivAt_id t).sub_const 1)

lemma shiftedFirst_hasDerivAt (t : ℝ) :
    HasDerivAt shiftedFirst (shiftedSecond t) t := by
  simpa only [Function.comp_def, mul_one] using!
    (first_hasDerivAt_second (t - 1)).comp t ((hasDerivAt_id t).sub_const 1)

lemma shifted_nonneg (t : ℝ) : 0 ≤ shifted t := smoothLoss_nonneg (t - 1)

lemma shifted_lt_one (t : ℝ) : shifted t < 1 := smoothLoss_lt_one (t - 1)

lemma shifted_abs_le_one (t : ℝ) : |shifted t| ≤ 1 := by
  rw [abs_of_nonneg (shifted_nonneg t)]
  exact (shifted_lt_one t).le

lemma shiftedFirst_abs_le_one (t : ℝ) : |shiftedFirst t| ≤ 1 :=
  first_abs_le_one (t - 1)

lemma shiftedSecond_abs_le_two (t : ℝ) : |shiftedSecond t| ≤ 2 :=
  second_abs_le_two (t - 1)

lemma shiftedFirst_continuous : Continuous shiftedFirst :=
  first_continuous.comp (continuous_id.sub continuous_const)

lemma shiftedSecond_continuous : Continuous shiftedSecond :=
  second_continuous.comp (continuous_id.sub continuous_const)

/-- The fixed loss bundled as a bounded continuous function. -/
def potential : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
  shifted shifted_contDiff.continuous 1 (fun t => by
    simpa only [Real.norm_eq_abs] using shifted_abs_le_one t)

/-- The true first derivative bundled as a bounded continuous function. -/
def potentialDeriv : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
  shiftedFirst shiftedFirst_continuous 1 (fun t => by
    simpa only [Real.norm_eq_abs] using shiftedFirst_abs_le_one t)

/-- The true second derivative bundled as a bounded continuous function. -/
def potentialSecond : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
  shiftedSecond shiftedSecond_continuous 2 (fun t => by
    simpa only [Real.norm_eq_abs] using shiftedSecond_abs_le_two t)

@[simp] lemma potential_apply (t : ℝ) : potential t = smoothLoss (t - 1) := rfl
@[simp] lemma potentialDeriv_apply (t : ℝ) :
    potentialDeriv t = 2 * (t - 1) / (1 + (t - 1) ^ 2) ^ 2 := rfl
@[simp] lemma potentialSecond_apply (t : ℝ) :
    potentialSecond t = (2 - 6 * (t - 1) ^ 2) / (1 + (t - 1) ^ 2) ^ 3 := rfl

lemma potential_formula (t : ℝ) :
    potential t = (t - 1) ^ 2 / (1 + (t - 1) ^ 2) := rfl

lemma potential_hasDerivAt (t : ℝ) : HasDerivAt potential (potentialDeriv t) t :=
  shifted_hasDerivAt t

lemma potentialDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt potentialDeriv (potentialSecond t) t := shiftedFirst_hasDerivAt t

lemma potential_norm_le_one : ‖potential‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by norm_num) _

lemma potentialDeriv_norm_le_one : ‖potentialDeriv‖ ≤ 1 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by norm_num) _

lemma potentialSecond_norm_le_two : ‖potentialSecond‖ ≤ 2 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by norm_num) _

/-- Exact integration with the empirical clipping estimate: the potential is
applied to predictions, while L1 and the moment condition use residuals. -/
theorem empirical_abs_sub_one_le {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℝ) {δ R K : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hmoment : (∑ i, |y i - 1| ^ (6 / 5 : ℝ)) ≤ K * n) :
    (∑ i, |y i - 1|) / n ≤ δ + (R / smoothLoss δ) *
      ((∑ i, potential (y i)) / n) + K / R ^ (1 / 5 : ℝ) := by
  simpa only [potential_apply] using!
    empirical_abs_le_smoothLoss_six_fifths hn (fun i => y i - 1) hδ hR hmoment

/-- A uniform loss threshold for the literal bundled potential, independent
of the number of observations and the predictions. -/
theorem exists_potential_threshold {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (n : ℕ), 0 < n → ∀ (y : Fin n → ℝ),
      (∑ i, |y i - 1| ^ (6 / 5 : ℝ)) ≤ K * n →
      (∑ i, potential (y i)) / n ≤ η →
      (∑ i, |y i - 1|) / n < ε := by
  obtain ⟨η, hη, h⟩ := exists_smoothLoss_threshold hK hε
  refine ⟨η, hη, ?_⟩
  intro n hn y hm hl
  exact h n hn (fun i => y i - 1) hm hl

/-- The bounded-C² Gibbs loss controls L1 on the same constrained candidates.
Only a genuine uniform residual moment bound remains as an analytic input. -/
theorem exists_small_L1_of_small_potential {α : Type*} {n : ℕ}
    (hn : 0 < n) (P : α → Prop) (y : α → Fin n → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hmoment : ∀ a, P a → (∑ i, |y a i - 1| ^ (6 / 5 : ℝ)) ≤ K * n)
    (hloss : ∀ η : ℝ, 0 < η → ∃ a, P a ∧ (∑ i, potential (y a i)) / n ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a, P a ∧ (∑ i, |y a i - 1|) / n < ε :=
  exists_small_L1_of_small_smoothLoss hn P (fun a i => y a i - 1)
    hK hmoment hloss hε

variable {κ : Type*} [Fintype κ]

/-- Actual bounded C² finite Gibbs data for any finite probability prior and
any nonnegative inverse temperature; no derivative/boundedness inputs remain. -/
def data2 (weight : κ → ℝ) (weight_nonneg : ∀ a, 0 ≤ weight a)
    (weight_sum : ∑ a, weight a = 1) (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    BMFiniteGibbsHessian.Data2 κ where
  weight := weight
  weight_nonneg := weight_nonneg
  weight_sum := weight_sum
  potential := potential
  potentialDeriv := potentialDeriv
  hasDeriv := potential_hasDerivAt
  beta := beta
  beta_nonneg := beta_nonneg
  potentialSecond := potentialSecond
  hasDeriv_second := potentialDeriv_hasDerivAt

@[simp] lemma data2_weight (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (data2 w hw hs β hβ).weight = w := rfl
@[simp] lemma data2_beta (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (data2 w hw hs β hβ).beta = β := rfl
@[simp] lemma data2_potential (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (data2 w hw hs β hβ).potential = potential := rfl
@[simp] lemma data2_potentialDeriv (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (data2 w hw hs β hβ).potentialDeriv = potentialDeriv := rfl
@[simp] lemma data2_potentialSecond (w : κ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (β : ℝ) (hβ : 0 ≤ β) :
    (data2 w hw hs β hβ).potentialSecond = potentialSecond := rfl

/-- A convenient one-state base data object retaining the exact same potential. -/
def unitData2 (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    BMFiniteGibbsHessian.Data2 Unit :=
  data2 (fun _ => 1) (fun _ => by norm_num) (by simp) beta beta_nonneg

@[simp] lemma unitData2_beta (β : ℝ) (hβ : 0 ≤ β) :
    (unitData2 β hβ).beta = β := rfl
@[simp] lemma unitData2_potential (β : ℝ) (hβ : 0 ≤ β) :
    (unitData2 β hβ).potential = potential := rfl
@[simp] lemma unitData2_potentialDeriv (β : ℝ) (hβ : 0 ≤ β) :
    (unitData2 β hβ).potentialDeriv = potentialDeriv := rfl
@[simp] lemma unitData2_potentialSecond (β : ℝ) (hβ : 0 ≤ β) :
    (unitData2 β hβ).potentialSecond = potentialSecond := rfl

#print axioms first_hasDerivAt_second
#print axioms second_abs_le_two
#print axioms potential_hasDerivAt
#print axioms potentialDeriv_hasDerivAt
#print axioms data2

end BMRationalLossData
