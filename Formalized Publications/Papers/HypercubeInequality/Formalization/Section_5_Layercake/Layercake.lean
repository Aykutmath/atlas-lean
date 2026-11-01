module

/-
# From binary labels to real heights (HI-LAYERCAKE, HI-THRESH-APPLY, HI-GAPID, HI-DET-ONESTEP)

Paper Section 5: threshold representation `B_i = ∫ (1_{B_i>t} - 1_{0>t}) dt`,
the `A_T` integral identity (the reference term drops out by the alternating
identity for the all-ones column), per-threshold application of HI-WEIGHTED
with Tonelli interchange, the gap identity, and the real-height determinant
inequality.
-/

public import Mathlib
public import Section_4_BernoulliCounting.Counting

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

section Threshold

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- Thresholded height `B_i^{(t)} = 1_{B_i > t}`. -/
@[expose] public noncomputable def thresh (t : ℝ) (i : Fin N) : ℝ :=
  if B i > t then 1 else 0

/-- Reference term `1_{0 > t}`. -/
@[expose] public noncomputable def threshRef (t : ℝ) : ℝ :=
  if (0 : ℝ) > t then 1 else 0

/-- Threshold probability `q(t) = ∑ p_i 1_{B_i > t}`. -/
@[expose] public noncomputable def qprob (t : ℝ) : ℝ :=
  pbar p (thresh B t)

/-- The threshold difference is a signed interval indicator. -/
public theorem threshDiff_eq_indicator (b : ℝ) :
    (fun t => (if b > t then (1 : ℝ) else 0) - (if (0 : ℝ) > t then 1 else 0))
    = if 0 ≤ b then (Set.Ico 0 b).indicator 1
      else fun t => -((Set.Ico b 0).indicator 1 t) := by
  by_cases hb : 0 ≤ b
  · simp only [hb, ite_true]
    funext t
    by_cases h1 : b > t <;> by_cases h0 : (0 : ℝ) > t
    · have hmem : t ∉ Set.Ico (0 : ℝ) b := by
        rw [Set.mem_Ico, not_and_or]
        exact Or.inl (by linarith)
      simp only [h1, h0, ite_true, Set.indicator_of_notMem hmem, sub_self]
    · have hmem : t ∈ Set.Ico (0 : ℝ) b := by
        rw [Set.mem_Ico]
        constructor <;> linarith
      simp only [h1, h0, ite_true, ite_false, Set.indicator_of_mem hmem,
        sub_zero, Pi.one_apply]
    · exfalso
      linarith
    · have hmem : t ∉ Set.Ico (0 : ℝ) b := by
        rw [Set.mem_Ico, not_and_or]
        exact Or.inr (by linarith)
      simp only [h1, h0, ite_false, Set.indicator_of_notMem hmem, sub_zero]
  · simp only [hb, ite_false]
    funext t
    by_cases h1 : b > t <;> by_cases h0 : (0 : ℝ) > t
    · have hmem : t ∉ Set.Ico b (0 : ℝ) := by
        rw [Set.mem_Ico, not_and_or]
        exact Or.inl (by linarith)
      simp only [h1, h0, ite_true, Set.indicator_of_notMem hmem, sub_self,
        neg_zero]
    · exfalso
      linarith
    · have hmem : t ∈ Set.Ico b (0 : ℝ) := by
        rw [Set.mem_Ico]
        constructor <;> linarith
      simp only [h1, h0, ite_false, ite_true, Set.indicator_of_mem hmem,
        Pi.one_apply, zero_sub]
    · have hmem : t ∉ Set.Ico b (0 : ℝ) := by
        rw [Set.mem_Ico, not_and_or]
        exact Or.inr (by linarith)
      simp only [h1, h0, ite_false, Set.indicator_of_notMem hmem, sub_zero,
        neg_zero]

/-- Threshold representation `b = ∫ (1_{b>t} - 1_{0>t}) dt`. -/
public theorem integral_threshDiff (b : ℝ) :
    (∫ t, ((if b > t then (1 : ℝ) else 0) - (if (0 : ℝ) > t then 1 else 0))
      ∂volume) = b := by
  rw [threshDiff_eq_indicator]
  by_cases hb : 0 ≤ b <;> simp only [hb, ite_true, ite_false]
  · have h : (∫ t, (Set.Ico (0 : ℝ) b).indicator 1 t ∂volume)
        = Measure.real volume (Set.Ico (0 : ℝ) b) :=
      integral_indicator_one measurableSet_Ico
    have hreal : Measure.real volume (Set.Ico (0 : ℝ) b)
        = (volume (Set.Ico (0 : ℝ) b)).toReal := rfl
    rw [hreal, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)] at h
    rw [h]
    ring
  · rw [integral_neg]
    have h : (∫ t, (Set.Ico b (0 : ℝ)).indicator 1 t ∂volume)
        = Measure.real volume (Set.Ico b (0 : ℝ)) :=
      integral_indicator_one measurableSet_Ico
    have hreal : Measure.real volume (Set.Ico b (0 : ℝ))
        = (volume (Set.Ico b (0 : ℝ))).toReal := rfl
    rw [hreal, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)] at h
    rw [h]
    ring

/-- Threshold differences are integrable. -/
public theorem integrable_threshDiff (b : ℝ) :
    Integrable
      (fun t => (if b > t then (1 : ℝ) else 0)
        - (if (0 : ℝ) > t then 1 else 0)) volume := by
  rw [threshDiff_eq_indicator]
  by_cases hb : 0 ≤ b <;> simp only [hb, ite_true, ite_false]
  · have hfin : volume (Set.Ico (0 : ℝ) b) ≠ ∞ := by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    exact (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const hfin (by simp))
  · have hfin : volume (Set.Ico b (0 : ℝ)) ≠ ∞ := by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    exact ((integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const hfin (by simp))).neg

/-- Threshold representation in `thresh` form. -/
public theorem integral_thresh (i : Fin N) :
    (∫ t, thresh B t i - threshRef t ∂volume) = B i := by
  simp only [thresh, threshRef]
  exact integral_threshDiff (B i)

/-- Integrability in `thresh` form. -/
public theorem integrable_thresh (i : Fin N) :
    Integrable (fun t => thresh B t i - threshRef t) volume := by
  simp only [thresh, threshRef]
  exact integrable_threshDiff (B i)

/-- Thresholded heights are binary. -/
public theorem thresh_binary (t : ℝ) :
    ∀ i, thresh B t i = 0 ∨ thresh B t i = 1 := by
  intro i
  simp only [thresh]
  by_cases h : B i > t <;> simp [h]

/-- The `A_T` matrix with an all-ones height column has determinant zero
(repeated all-ones columns). -/
public theorem detAT_ones_eq_zero (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    detAT Yatom (fun _ => 1) T hT = 0 := by
  have hcol : ∀ r, detATMat Yatom (fun _ => 1) T hT r 0
      = detATMat Yatom (fun _ => 1) T hT r (Fin.succ 0) := by
    intro r
    simp only [detATMat, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
  have hne : (0 : Fin (m + 2)) ≠ Fin.succ 0 := by simp
  simp only [detAT]
  exact Matrix.det_zero_of_column_eq hne hcol

/-- Alternating projected-determinant identity `∑ (-1)^r D(T∖{t_r}) = 0`. -/
public theorem alt_detOf_sum_zero (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) = 0 := by
  have h0 : detAT Yatom (fun _ => 1) T hT = 0 :=
    detAT_ones_eq_zero Yatom T hT
  rw [detAT_eq_expansion] at h0
  simp only [mul_one] at h0
  exact h0

end Threshold

section LayercakeAT

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- Threshold slices of `A_T` expand through the threshold differences
(the reference term drops out by the alternating identity). -/
public theorem detAT_thresh_eq_sum (T : Finset (Fin N))
    (hT : T.card = m + 2) (t : ℝ) :
    detAT Yatom (thresh B t) T hT
      = ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
        * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) := by
  rw [detAT_eq_expansion]
  have halt := alt_detOf_sum_zero Yatom T hT
  have hsplit : (∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
          * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
          * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)))
      = (∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
          * thresh B t (T.orderEmbOfFin hT r)
          * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)))
        - threshRef t * (∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
          * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsplit, halt, mul_zero, sub_zero]

/-- Threshold slices of `A_T` are integrable. -/
public theorem integrable_detAT_thresh (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    Integrable (fun t => detAT Yatom (thresh B t) T hT) volume := by
  have hfun : (fun t => detAT Yatom (thresh B t) T hT)
      = fun t => ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
        * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) :=
    funext (fun t => detAT_thresh_eq_sum Yatom B T hT t)
  rw [hfun]
  exact integrable_finsetSum _ (fun r _ =>
    ((integrable_thresh B _).const_mul _).mul_const _)

/-- HI-LAYERCAKE core: `A_T(B) = ∫ A_T(B^{(t)}) dt`. -/
public theorem detAT_eq_integral_thresh (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    detAT Yatom B T hT
      = ∫ t, detAT Yatom (thresh B t) T hT ∂volume := by
  have hfun : (fun t => detAT Yatom (thresh B t) T hT)
      = fun t => ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val : ℕ)
        * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) :=
    funext (fun t => detAT_thresh_eq_sum Yatom B T hT t)
  have hper : ∀ r : Fin (m + 2),
      (∫ t, (-1 : ℝ) ^ (r.val : ℕ)
        * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) ∂volume)
      = (-1 : ℝ) ^ (r.val : ℕ) * B (T.orderEmbOfFin hT r)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) := by
    intro r
    have hK : (fun t => (-1 : ℝ) ^ (r.val : ℕ)
          * (thresh B t (T.orderEmbOfFin hT r) - threshRef t)
          * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)))
        = fun t => ((-1 : ℝ) ^ (r.val : ℕ)
          * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)))
          * (thresh B t (T.orderEmbOfFin hT r) - threshRef t) := by
      funext t
      ring
    rw [hK, integral_const_mul, integral_thresh B _]
    ring
  rw [hfun, integral_finsetSum _ (fun r _ =>
    ((integrable_thresh B _).const_mul _).mul_const _)]
  rw [Finset.sum_congr rfl (fun r _ => hper r)]
  rw [← detAT_eq_expansion]

/-- `|A_T(B)| ≤ ∫ |A_T(B^{(t)})| dt`. -/
public theorem abs_detAT_le_integral_thresh (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    |detAT Yatom B T hT|
      ≤ ∫ t, |detAT Yatom (thresh B t) T hT| ∂volume := by
  rw [detAT_eq_integral_thresh Yatom B T hT]
  simp only [← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm _

end LayercakeAT

section ApplyIID

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- Pairwise expansion `q(1-q) = ∑_{i,j} p_i p_j u_i (1-u_j)`. -/
public theorem qprob_mul_one_sub (t : ℝ) (hsum : ∑ i, p i = 1) :
    qprob p B t * (1 - qprob p B t)
    = ∑ i, ∑ j, p i * p j * (thresh B t i * (1 - thresh B t j)) := by
  have h1 : 1 - qprob p B t = ∑ j, p j * (1 - thresh B t j) := by
    simp only [qprob, pbar]
    conv_lhs => rw [← hsum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : qprob p B t * (1 - qprob p B t)
      = (∑ i, p i * thresh B t i) * (∑ j, p j * (1 - thresh B t j)) := by
    rw [h1]
    simp only [qprob, pbar]
  rw [h2, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The pairwise threshold product is an interval indicator. -/
public theorem thresh_mul_indicator (t : ℝ) (i j : Fin N) :
    thresh B t i * (1 - thresh B t j)
    = (Set.Ico (B j) (B i)).indicator 1 t := by
  simp only [thresh]
  by_cases hi : B i > t <;> by_cases hj : B j > t
  · have hmem : t ∉ Set.Ico (B j) (B i) := by
      rw [Set.mem_Ico, not_and_or]
      exact Or.inl (by linarith)
    simp only [hi, hj, ite_true, Set.indicator_of_notMem hmem, sub_self,
      mul_zero]
  · have hmem : t ∈ Set.Ico (B j) (B i) := by
      rw [Set.mem_Ico]
      constructor <;> linarith
    simp only [hi, hj, ite_true, ite_false, Set.indicator_of_mem hmem,
      Pi.one_apply, sub_zero, mul_one]
  · have hmem : t ∉ Set.Ico (B j) (B i) := by
      rw [Set.mem_Ico, not_and_or]
      exact Or.inr (by linarith)
    simp only [hi, hj, ite_false, ite_true, Set.indicator_of_notMem hmem,
      zero_mul]
  · have hmem : t ∉ Set.Ico (B j) (B i) := by
      rw [Set.mem_Ico, not_and_or]
      exact Or.inr (by linarith)
    simp only [hi, hj, ite_false, Set.indicator_of_notMem hmem, zero_mul]

/-- Pairwise terms in indicator form. -/
public theorem threshPair_eq_indicator (i j : Fin N) :
    (fun t => p i * p j * (thresh B t i * (1 - thresh B t j)))
    = fun t => (p i * p j) * (Set.Ico (B j) (B i)).indicator 1 t := by
  funext t
  rw [thresh_mul_indicator]

/-- Pairwise terms are integrable. -/
public theorem integrable_threshPair (i j : Fin N) :
    Integrable (fun t => p i * p j * (thresh B t i * (1 - thresh B t j)))
      volume := by
  rw [threshPair_eq_indicator]
  have hfin : volume (Set.Ico (B j) (B i)) ≠ ∞ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  exact (((integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const hfin (by simp))).const_mul _)

/-- `q(1-q)` is integrable. -/
public theorem integrable_qprob (hsum : ∑ i, p i = 1) :
    Integrable (fun t => qprob p B t * (1 - qprob p B t)) volume := by
  have hfun : (fun t => qprob p B t * (1 - qprob p B t))
      = fun t => ∑ i, ∑ j, p i * p j * (thresh B t i * (1 - thresh B t j)) :=
    funext (fun t => qprob_mul_one_sub p B t hsum)
  rw [hfun]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => integrable_threshPair p B i j))

/-- Weighted threshold slices are integrable. -/
public theorem integrable_wAT_thresh (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    Integrable (fun t => atomWeight p T * |detAT' Yatom (thresh B t) T|)
      volume := by
  have hfun : (fun t => atomWeight p T * |detAT' Yatom (thresh B t) T|)
      = fun t => atomWeight p T * |detAT Yatom (thresh B t) T hT| := by
    funext t
    rw [detAT'_eq Yatom (thresh B t) T hT]
  rw [hfun]
  exact (integrable_detAT_thresh Yatom B T hT).abs.const_mul _

/-- The summed threshold integrand is integrable. -/
public theorem integrable_sum_AT_thresh :
    Integrable (fun t => ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
      atomWeight p T * |detAT' Yatom (thresh B t) T|) volume :=
  integrable_finsetSum _ (fun T hT =>
    integrable_wAT_thresh p Yatom B T (Finset.mem_powersetCard.mp hT).2)

/-- HI-THRESH-APPLY + layer-cake assembly:
`E|A(B)| ≤ (∫ q(1-q)) E∑_r |D_r|`. -/
public theorem layercake_bound (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) :
    (∑ F : Fin (m + 2) → Fin N, ordTermA p Yatom B F)
      ≤ (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := by
  classical
  have hcount := count_ordered_A p Yatom B
  have hstep1 : ∀ T ∈ Finset.powersetCard (m + 2)
      (Finset.univ : Finset (Fin N)),
      atomWeight p T * |detAT' Yatom B T|
      ≤ atomWeight p T
        * ∫ t, |detAT' Yatom (thresh B t) T| ∂volume := by
    intro T hT
    have hTc : T.card = m + 2 := (Finset.mem_powersetCard.mp hT).2
    have hfun : (fun t => |detAT' Yatom (thresh B t) T|)
        = fun t => |detAT Yatom (thresh B t) T hTc| := by
      funext t
      rw [detAT'_eq Yatom (thresh B t) T hTc]
    rw [detAT'_eq Yatom B T hTc, hfun]
    exact mul_le_mul_of_nonneg_left
      (abs_detAT_le_integral_thresh Yatom B T hTc)
      (atomWeight_nonneg p hpos T)
  have hsum1 : (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom B T|)
      ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * ∫ t, |detAT' Yatom (thresh B t) T| ∂volume :=
    Finset.sum_le_sum hstep1
  have hton : (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * ∫ t, |detAT' Yatom (thresh B t) T| ∂volume)
      = ∫ t, (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom (thresh B t) T|) ∂volume := by
    rw [integral_finsetSum _ (fun T hT =>
      integrable_wAT_thresh p Yatom B T (Finset.mem_powersetCard.mp hT).2)]
    apply Finset.sum_congr rfl
    intro T _
    rw [integral_const_mul]
  have hWt : ∀ t : ℝ, (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom (thresh B t) T|)
      ≤ qprob p B t * (1 - qprob p B t)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U| := by
    intro t
    have hW := weighted_bernoulli_inequality p Yatom (thresh B t) hpos hsum
      (thresh_binary B t)
    simpa [qprob] using hW
  have hmono : (∫ t, (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom (thresh B t) T|) ∂volume)
      ≤ ∫ t, (qprob p B t * (1 - qprob p B t)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U|) ∂volume :=
    integral_mono_ae (integrable_sum_AT_thresh p Yatom B)
      ((integrable_qprob p B hsum).mul_const _)
      (Filter.Eventually.of_forall hWt)
  have hfactor : (∫ t, (qprob p B t * (1 - qprob p B t)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U|) ∂volume)
      = (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U| :=
    integral_mul_const _ _
  have hchain : (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom B T|)
      ≤ (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U| :=
    calc (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
            atomWeight p T * |detAT' Yatom B T|)
        ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
            atomWeight p T * ∫ t, |detAT' Yatom (thresh B t) T| ∂volume :=
          hsum1
      _ = ∫ t, (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
            atomWeight p T * |detAT' Yatom (thresh B t) T|) ∂volume := hton
      _ ≤ ∫ t, (qprob p B t * (1 - qprob p B t)
            * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
              atomWeight p U * |detOf' Yatom U|) ∂volume := hmono
      _ = (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
            * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
              atomWeight p U * |detOf' Yatom U| := hfactor
  have hK : (0 : ℝ) ≤ ((m + 2)! : ℝ) := Nat.cast_nonneg _
  have hfinal : ((m + 2)! : ℝ)
        * ((∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * |detOf' Yatom U|)
      = (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := by
    have hO : (∑ r : Fin (m + 2), omitSum p Yatom r)
        = ((m + 2 : ℕ) : ℝ)
          * ∑ G : Fin (m + 1) → Fin N, ordTermD p Yatom G := by
      simp only [omitSum_eq p Yatom _ hsum]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfact : ((m + 2)! : ℝ) = ((m + 2 : ℕ) : ℝ) * ((m + 1)! : ℝ) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.cast_mul]
    rw [hO, hfact, count_ordered_D p Yatom]
    ring
  calc (∑ F : Fin (m + 2) → Fin N, ordTermA p Yatom B F)
      = ((m + 2)! : ℝ) * ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom B T| := hcount
    _ ≤ ((m + 2)! : ℝ)
        * ((∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * |detOf' Yatom U|) :=
      mul_le_mul_of_nonneg_left hchain hK
    _ = (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := hfinal

end ApplyIID

section GapDet

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- Finite-law gap `E|B - B'|`. -/
@[expose] public noncomputable def gapPair : ℝ :=
  ∑ i, ∑ j, p i * p j * |B i - B j|

/-- Interval indicators integrate to the positive part. -/
public theorem integral_indIco (a b : ℝ) :
    (∫ t, (Set.Ico a b).indicator 1 t ∂volume) = max (b - a) 0 := by
  have h : (∫ t, (Set.Ico a b).indicator 1 t ∂volume)
      = Measure.real volume (Set.Ico a b) :=
    integral_indicator_one measurableSet_Ico
  have hreal : Measure.real volume (Set.Ico a b)
      = (volume (Set.Ico a b)).toReal := rfl
  rw [hreal, Real.volume_Ico] at h
  by_cases hab : a ≤ b
  · rw [ENNReal.toReal_ofReal (by linarith)] at h
    rw [h, max_eq_left (show (0 : ℝ) ≤ b - a by linarith)]
  · have hle : b - a ≤ 0 := by linarith
    rw [ENNReal.ofReal_of_nonpos hle, ENNReal.toReal_zero] at h
    rw [h, max_eq_right hle]

/-- `|x| = (x)₊ + (-x)₊`. -/
public theorem abs_eq_max_add (x : ℝ) :
    |x| = max x 0 + max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h,
      max_eq_right (show -x ≤ 0 by linarith), add_zero]
  · rw [abs_of_nonpos h, max_eq_right h,
      max_eq_left (show (0 : ℝ) ≤ -x by linarith), zero_add]

/-- HI-GAPID: `E|B-B'| = 2 ∫ q(1-q)`. -/
public theorem gap_identity (hsum : ∑ i, p i = 1) :
    gapPair p B
      = 2 * ∫ t, qprob p B t * (1 - qprob p B t) ∂volume := by
  classical
  have hInt : (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
      = ∑ i, ∑ j, p i * p j * max (B i - B j) 0 := by
    have hfun : (fun t => qprob p B t * (1 - qprob p B t))
        = fun t => ∑ i, ∑ j,
          p i * p j * (thresh B t i * (1 - thresh B t j)) :=
      funext (fun t => qprob_mul_one_sub p B t hsum)
    rw [hfun, integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => integrable_threshPair p B i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => integrable_threshPair p B i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [threshPair_eq_indicator, integral_const_mul, integral_indIco]
  have hpair : gapPair p B
      = 2 * ∑ i, ∑ j, p i * p j * max (B i - B j) 0 := by
    simp only [gapPair]
    have hterm : ∀ i j : Fin N,
        p i * p j * |B i - B j|
        = p i * p j * max (B i - B j) 0
          + p i * p j * max (B j - B i) 0 := by
      intro i j
      have habs := abs_eq_max_add (B i - B j)
      have hneg : max (-(B i - B j)) 0 = max (B j - B i) 0 := by
        congr 1
        ring
      rw [habs, hneg]
      ring
    rw [Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => hterm i j))]
    simp only [Finset.sum_add_distrib]
    have hprod : ∀ F : Fin N → Fin N → ℝ,
        (∑ i, ∑ j, F i j)
        = ∑ q : Fin N × Fin N, F q.1 q.2 :=
      fun F => (Fintype.sum_prod_type
        (fun q : Fin N × Fin N => F q.1 q.2)).symm
    have hswap : (∑ i, ∑ j, p i * p j * max (B j - B i) 0)
        = ∑ i, ∑ j, p i * p j * max (B i - B j) 0 := by
      rw [hprod, hprod]
      have h := Equiv.sum_comp (Equiv.prodComm _ _)
        (fun q : Fin N × Fin N => p q.1 * p q.2 * max (B q.1 - B q.2) 0)
      rw [← h]
      apply Finset.sum_congr rfl
      intro q _
      show p q.1 * p q.2 * max (B q.2 - B q.1) 0
        = p q.2 * p q.1 * max (B q.2 - B q.1) 0
      ring
    rw [hswap]
    ring
  rw [hpair, hInt]

/-- HI-DET-ONESTEP: `E|A| ≤ (1/2) E|B-B'| E∑_r |D_r|`. -/
public theorem det_onestep (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) :
    (∑ F : Fin (m + 2) → Fin N, ordTermA p Yatom B F)
      ≤ (1 / 2) * gapPair p B
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := by
  have hL := layercake_bound p Yatom B hpos hsum
  have hG := gap_identity p B hsum
  have hI : (∫ t, qprob p B t * (1 - qprob p B t) ∂volume)
      = (1 / 2) * gapPair p B := by
    rw [hG]
    ring
  rw [hI] at hL
  exact hL

end GapDet

end HypercubeInequality
