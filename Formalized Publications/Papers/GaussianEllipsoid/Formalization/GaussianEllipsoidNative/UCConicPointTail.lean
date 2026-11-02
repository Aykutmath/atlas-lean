import UCQuadraticSmallBall
import GaussianEllipsoid.ConicNets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GaussianEllipsoid.UCConicPointTail
open UCQuadraticSmallBall UCProductConcentration

def left {n : ℕ} (i : Fin (n/2)) : Fin n := ⟨i, by omega⟩
def right {n : ℕ} (i : Fin (n/2)) : Fin n := ⟨n/2+i, by omega⟩

theorem left_injective (n : ℕ) : Function.Injective (@left n) := by
  intro i j h; apply Fin.ext; exact congrArg (fun k : Fin n => k.val) h

theorem right_injective (n : ℕ) : Function.Injective (@right n) := by
  intro i j h; apply Fin.ext; have hh := congrArg Fin.val h
  simp only [right] at hh; omega

theorem left_ne_right {n : ℕ} (i : Fin (n/2)) : left i ≠ right i := by
  intro h; have hh := congrArg Fin.val h
  simp only [left, right] at hh; have := i.isLt; omega

def pairLoss {d n : ℕ} (A : Square d) (x : Sample d n) (i : Fin (n/2)) : ℝ :=
  clip (row A (x (left i))-row A (x (right i)))

def pairMean {d n : ℕ} (A : Square d) (x : Sample d n) : ℝ :=
  (1/(n:ℝ))*∑ i, pairLoss A x i

theorem measurable_pairLoss {d n : ℕ} (A : Square d) (i : Fin (n/2)) :
    Measurable (fun x : Sample d n => pairLoss A x i) := by
  exact measurable_clip.comp (((measurable_row A).comp (measurable_pi_apply (left i))).sub
    ((measurable_row A).comp (measurable_pi_apply (right i))))

theorem pairLoss_integrable {d n : ℕ} (A : Square d) (i : Fin (n/2)) :
    Integrable (fun x : Sample d n => pairLoss A x i) (gaussianSampleLaw d n) :=
  integrable_of_abs_bound (M := 1) (measurable_pairLoss A i) (fun x => by
    unfold pairLoss
    rw [abs_of_nonneg (clip_nonneg _)]; exact clip_le_one _)

theorem integral_pairLoss {d n : ℕ} (A : Square d) (i : Fin (n/2)) :
    (∫ x : Sample d n, pairLoss A x i ∂gaussianSampleLaw d n) =
      ∫ z : Vector d × Vector d, clip (row A z.1-row A z.2)
        ∂(gaussianVectorLaw d).prod (gaussianVectorLaw d) := by
  let f : Sample d n → Vector d × Vector d := fun x => (x (left i),x (right i))
  have hf : Measurable f := (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hm : (gaussianSampleLaw d n).map f =
      (gaussianVectorLaw d).prod (gaussianVectorLaw d) := by
    have h := IndepFun.map_prod_eq_prod_map_map (measurable_pi_apply (left i)).aemeasurable
      (measurable_pi_apply (right i)).aemeasurable
      ((gaussianRows_independent d n).indepFun (left_ne_right i))
    simpa only [gaussianRow_map] using h
  have hg : Measurable (fun z : Vector d × Vector d => clip (row A z.1-row A z.2)) :=
    measurable_clip.comp (((measurable_row A).comp measurable_fst).sub
      ((measurable_row A).comp measurable_snd))
  rw [← hm, integral_map_of_stronglyMeasurable hf hg.stronglyMeasurable]
  rfl

theorem pairMean_expectation {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (A : Square d) (hA : A.transpose = A) (hF : frobeniusNorm A = 1) :
    (1/30000000:ℝ) ≤ ∫ x, pairMean A x ∂gaussianSampleLaw d n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hratio : (n:ℝ) ≤ 3*(n/2:ℕ) := by exact_mod_cast (show n ≤ 3*(n/2) by omega)
  have hm := paired_clip_mean hd A hA hF
  simp only [pairMean]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => pairLoss_integrable A i)]
  simp only [integral_pairLoss, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [one_div]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hnR).mpr
  have hh := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (n/2) : (0:ℝ)≤(n/2:ℕ))
  nlinarith

theorem sum_embedding_le {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) : (∑ j, f (e j)) ≤ ∑ i, f i := by
  classical
  rw [← Finset.sum_image (fun i _ j _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hf i)

theorem pairMean_abs_le {d n : ℕ} (A : Square d) (x : Sample d n) : |pairMean A x| ≤ 1 := by
  have hnon : 0 ≤ pairMean A x := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => clip_nonneg _
  rw [abs_of_nonneg hnon]
  calc
    _ ≤ (1/(n:ℝ))*∑ _i : Fin (n/2), (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => clip_le_one _) (by positivity)
    _ ≤ (1/(n:ℝ))*∑ _i : Fin n, (1:ℝ) := by
      exact mul_le_mul_of_nonneg_left (sum_embedding_le (@left n) (left_injective n)
        (fun _ => (1:ℝ)) (fun _ => zero_le_one)) (by positivity)
    _ ≤ 1 := by simpa [div_eq_mul_inv, mul_comm] using div_self_le_one (n:ℝ)

theorem pairMean_boundedDifferences {d n : ℕ} (A : Square d) :
    boundedDifferences (pairMean (n := n) A) (2/(n:ℝ)) := by
  classical
  intro x j y
  have hp (i : Fin (n/2)) : |pairLoss A (Function.update x j y) i-pairLoss A x i| ≤
      (if left i=j then 1 else 0)+(if right i=j then 1 else 0) := by
    have hu := clip_le_one (row A ((Function.update x j y) (left i))-
      row A ((Function.update x j y) (right i)))
    have hl := clip_nonneg (row A ((Function.update x j y) (left i))-
      row A ((Function.update x j y) (right i)))
    have hu' := clip_le_one (row A (x (left i))-row A (x (right i)))
    have hl' := clip_nonneg (row A (x (left i))-row A (x (right i)))
    have hab : |pairLoss A (Function.update x j y) i-pairLoss A x i| ≤ 1 := by
      apply abs_le.mpr
      unfold pairLoss
      constructor <;> linarith
    by_cases h1 : left i=j <;> by_cases h2 : right i=j
    · simp only [h1,h2,ite_true]; linarith
    · simpa only [h1,h2,ite_true,ite_false,add_zero] using hab
    · simpa only [h1,h2,ite_true,ite_false,zero_add] using hab
    · simp [pairLoss, Function.update_of_ne h1, Function.update_of_ne h2, h1, h2]
  have hleft : (∑ i : Fin (n/2), if left i=j then (1:ℝ) else 0) ≤ 1 := by
    have h := sum_embedding_le (@left n) (left_injective n)
      (fun i => if i=j then (1:ℝ) else 0) (fun i => by split_ifs <;> norm_num)
    simpa using h
  have hright : (∑ i : Fin (n/2), if right i=j then (1:ℝ) else 0) ≤ 1 := by
    have h := sum_embedding_le (@right n) (right_injective n)
      (fun i => if i=j then (1:ℝ) else 0) (fun i => by split_ifs <;> norm_num)
    simpa using h
  calc
    _ = (1/(n:ℝ))*|∑ i, (pairLoss A (Function.update x j y) i-pairLoss A x i)| := by
      rw [pairMean,pairMean, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ)≤1/(n:ℝ))]
    _ ≤ (1/(n:ℝ))*∑ i, |pairLoss A (Function.update x j y) i-pairLoss A x i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1/(n:ℝ))*∑ i, ((if left i=j then 1 else 0)+(if right i=j then 1 else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hp i) (by positivity)
    _ ≤ (1/(n:ℝ))*2 := by
      rw [Finset.sum_add_distrib]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end GaussianEllipsoid.UCConicPointTail

namespace GaussianEllipsoid.UCConicPointTail
open UCQuadraticSmallBall UCProductConcentration

theorem measurable_pairMean {d n : ℕ} (A : Square d) :
    Measurable (pairMean (n := n) A) :=
  measurable_const.mul (Finset.measurable_sum _ (fun i _ => measurable_pairLoss A i))

theorem pairMean_le_margin {d n : ℕ} (A : Square d) (x : Sample d n) :
    pairMean A x ≤ 2*conicMargin x A := by
  have hp (i : Fin (n/2)) : pairLoss A x i ≤
      |center (measurementQ x A) (left i)|+|center (measurementQ x A) (right i)| := by
    apply (clip_le_abs _).trans
    have he : row A (x (left i))-row A (x (right i)) =
        center (measurementQ x A) (left i)-center (measurementQ x A) (right i) := by
      simp only [center, measurementQ, row]
      ring
    rw [he]
    exact abs_sub _ _
  have hleft := sum_embedding_le (@left n) (left_injective n)
    (fun j => |center (measurementQ x A) j|) (fun j => abs_nonneg _)
  have hright := sum_embedding_le (@right n) (right_injective n)
    (fun j => |center (measurementQ x A) j|) (fun j => abs_nonneg _)
  calc
    _ ≤ (1/(n:ℝ))*∑ i, (|center (measurementQ x A) (left i)|+
        |center (measurementQ x A) (right i)|) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hp i) (by positivity)
    _ ≤ (1/(n:ℝ))*(2*∑ j, |center (measurementQ x A) j|) := by
      rw [Finset.sum_add_distrib]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by unfold conicMargin l1Size; ring

def pointMargin : ℝ := 1/120000000
def pointRate : ℝ := 1/28800000000000000

theorem pointMargin_pos : 0 < pointMargin := by norm_num [pointMargin]
theorem pointRate_pos : 0 < pointRate := by norm_num [pointRate]

/-- Genuine exponential lower tail for the centered conic margin of one
arbitrary symmetric Frobenius-unit test; constants do not depend on rank. -/
theorem conicMargin_lower_tail {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (A : Square d) (hA : A.transpose = A) (hF : frobeniusNorm A = 1) :
    (gaussianSampleLaw d n).real {x | conicMargin x A < pointMargin} ≤
      Real.exp (-pointRate*(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have htail := product_lower_tail (gaussianVectorLaw d) n (pairMean A)
    (measurable_pairMean A) 1 (2/(n:ℝ)) (pairMean_abs_le A) (by positivity)
    (pairMean_boundedDifferences A) (1/60000000) (by norm_num)
  have hsub : {x : Sample d n | conicMargin x A < pointMargin} ⊆
      {x | pairMean A x < (∫ y, pairMean A y ∂productLaw (gaussianVectorLaw d) n)-1/60000000} := by
    intro x hx
    have hmean := pairMean_expectation hd hn A hA hF
    have hmargin := pairMean_le_margin A x
    change conicMargin x A < pointMargin at hx
    change pairMean A x < _
    dsimp [productLaw] at *
    unfold pointMargin at hx
    change _ ≤ ∫ y, pairMean A y ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d) at hmean
    linarith
  have h := (measureReal_mono (μ := gaussianSampleLaw d n) hsub).trans htail
  apply h.trans_eq
  congr 1
  unfold pointRate
  field_simp
  <;> ring

#print axioms conicMargin_lower_tail
end GaussianEllipsoid.UCConicPointTail
