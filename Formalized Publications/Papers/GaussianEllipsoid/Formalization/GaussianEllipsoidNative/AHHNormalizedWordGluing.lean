import AHHRankOneTrace
import AHHNormalizedWordBridge
import AHHGaussianWordIndependence

/-! Exact one-factor trace gluing and cyclicity for the manuscript's actual
normalized complex Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators Matrix

namespace AHHGaussian

theorem normalizedWordTrace_cyclic (n h : ℕ) (x : PairEntries n h)
    (w v : List (Fin n)) :
    Matrix.trace (normalizedWordMatrix n h x (w ++ v)) =
      Matrix.trace (normalizedWordMatrix n h x (v ++ w)) := by
  simp only [normalizedWordMatrix, List.map_append, List.prod_append]
  exact Matrix.trace_mul_comm _ _

theorem normalizedWordTrace_glue (n h : ℕ) (x : PairEntries n h)
    (s : Fin n) (U V X Y : List (Fin n)) :
    Matrix.trace (normalizedWordMatrix n h x (U ++ [s] ++ V)) *
      Matrix.trace (normalizedWordMatrix n h x (X ++ [s] ++ Y)) =
        Matrix.trace (normalizedWordMatrix n h x (U ++ [s] ++ Y ++ X ++ [s] ++ V)) := by
  have hh := AHH.rankOne_trace_glue
    (fun j => normalizedFactor n h true x s j)
    (fun j => star (normalizedFactor n h true x s j))
    (normalizedWordMatrix n h x U) (normalizedWordMatrix n h x V)
    (normalizedWordMatrix n h x X) (normalizedWordMatrix n h x Y)
  have hP : Matrix.vecMulVec
      (fun j => normalizedFactor n h true x s j)
      (fun j => star (normalizedFactor n h true x s j)) = normalizedProjector n h x s := rfl
  rw [hP] at hh
  simpa only [normalizedWordMatrix, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hh

theorem normalizedWordTrace_glue_integral (n h : ℕ)
    (s : Fin n) (U V X Y : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x (U ++ [s] ++ V)) *
      Matrix.trace (normalizedWordMatrix n h x (X ++ [s] ++ Y)) ∂pairGaussianLaw n h) =
        ∫ x, Matrix.trace
          (normalizedWordMatrix n h x (U ++ [s] ++ Y ++ X ++ [s] ++ V))
          ∂pairGaussianLaw n h := by
  simp_rw [normalizedWordTrace_glue]

theorem normalizedWordTrace_disjoint_integral (n h : ℕ)
    (w v : List (Fin n)) (hd : List.Disjoint w v) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x w) *
      Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h) =
        (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h) *
          (∫ x, Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h) := by
  rw [normalizedWordTrace_mul_integral, normalizedWordTrace_integral,
    normalizedWordTrace_integral, AHH.gaussian_wordTrace_integral_mul_of_disjoint w v hd]
  rw [pow_add]
  push_cast
  ring

theorem normalizedWordTrace_merge (n h : ℕ) (x : PairEntries n h)
    (s : Fin n) (U A B : List (Fin n)) :
    Matrix.trace (normalizedWordMatrix n h x (s :: U)) *
      Matrix.trace (normalizedWordMatrix n h x (A ++ s :: B)) =
      Matrix.trace (normalizedWordMatrix n h x ((s :: U) ++ (s :: B) ++ A)) := by
  have hg := normalizedWordTrace_glue n h x s [] U A B
  simp only [List.nil_append, List.append_assoc, List.singleton_append] at hg
  rw [hg]
  have hc := normalizedWordTrace_cyclic n h x ([s] ++ B ++ A) ([s] ++ U)
  simpa only [List.append_assoc, List.singleton_append] using hc

def normalizedWordMean (n h : ℕ) (w : List (Fin n)) : ℝ :=
  (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h).re

def normalizedWordPairMean (n h : ℕ) (w v : List (Fin n)) : ℝ :=
  (∫ x, Matrix.trace (normalizedWordMatrix n h x w) *
    Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h).re

theorem normalizedWordMean_nil (n h : ℕ) : normalizedWordMean n h [] = h := by
  simp [normalizedWordMean, normalizedWordMatrix]

theorem normalizedWordMean_cyclic (n h : ℕ) (w v : List (Fin n)) :
    normalizedWordMean n h (w ++ v) = normalizedWordMean n h (v ++ w) := by
  unfold normalizedWordMean
  simp_rw [normalizedWordTrace_cyclic n h _ w v]

theorem normalizedWordPairMean_merge (n h : ℕ)
    (s : Fin n) (U A B : List (Fin n)) :
    normalizedWordPairMean n h (s :: U) (A ++ s :: B) =
      normalizedWordMean n h ((s :: U) ++ (s :: B) ++ A) := by
  unfold normalizedWordPairMean normalizedWordMean
  simp_rw [normalizedWordTrace_merge]

theorem normalizedWordPairMean_glue (n h : ℕ)
    (s : Fin n) (U V X Y : List (Fin n)) :
    normalizedWordPairMean n h (U ++ [s] ++ V) (X ++ [s] ++ Y) =
      normalizedWordMean n h (U ++ [s] ++ Y ++ X ++ [s] ++ V) := by
  unfold normalizedWordPairMean normalizedWordMean
  rw [normalizedWordTrace_glue_integral]

theorem normalizedWordPairMean_disjoint (n h : ℕ)
    (w v : List (Fin n)) (hd : List.Disjoint w v) :
    normalizedWordPairMean n h w v = normalizedWordMean n h w * normalizedWordMean n h v := by
  unfold normalizedWordPairMean normalizedWordMean
  rw [normalizedWordTrace_disjoint_integral n h w v hd, Complex.mul_re,
    normalizedWordTrace_integral_im_zero, normalizedWordTrace_integral_im_zero]
  ring

theorem normalizedWordMean_nonneg (n h : ℕ) (w : List (Fin n)) :
    0 ≤ normalizedWordMean n h w := normalizedWordTrace_integral_re_nonneg n h w

theorem normalizedWordPairMean_nonneg (n h : ℕ) (w v : List (Fin n)) :
    0 ≤ normalizedWordPairMean n h w v := normalizedWordTrace_mul_integral_re_nonneg n h w v

end AHHGaussian
