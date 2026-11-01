import Section_10_Zonoid.Hypercube.Main
import Section_10_Zonoid.Hypercube.FiniteAtomicGeneric
import Section_10_Zonoid.Cor101.Normalization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Finite probability and determinant bridges for Corollary 10.1.

This module uses the actual finite atomic law, its first moments, and the
proved random-simplex theorem. No volume formula for zonotopes is assumed or
asserted here. In particular, `finite_determinant_bound` is not itself the
paper-facing zonoid projection inequality.

The ambient coordinate model is `Hypercube.Paper.Point d = Fin d -> Real`.
The existing `Hypercube.Representation` module bridges this model to Euclidean
space. Distinct labels are allowed to represent coincident points; zero
probabilities are also allowed throughout the finite-law results.
-/

noncomputable section

open MeasureTheory

namespace Cor101.FiniteBridge

open Hypercube

/-- The actual finitely supported law on the projected points. -/
def projectedLaw {N d : Nat} (q : Fin N -> Real)
    (z : Fin N -> Paper.Point d) : Measure (Paper.Point d) :=
  FiniteAtomicGeneric.atomicLaw q z

theorem projectedLaw_probability {N d : Nat} (q : Fin N -> Real)
    (z : Fin N -> Paper.Point d) (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum Finset.univ q = 1) :
    IsProbabilityMeasure (projectedLaw q z) := by
  let _ := FiniteAtomicGeneric.labelMeasure_isProbability q hq hqsum
  unfold projectedLaw FiniteAtomicGeneric.atomicLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable z).aemeasurable).mpr inferInstance

/-- Finiteness of the support discharges every moment assumption. -/
theorem projectedLaw_first_moments {N d : Nat} (q : Fin N -> Real)
    (z : Fin N -> Paper.Point d) :
    Paper.finiteCoordinateFirstMoments (projectedLaw q z) := by
  intro j
  have hcoord : Measurable (fun x : Paper.Point d => |x j|) :=
    continuous_abs.measurable.comp (continuous_apply j).measurable
  unfold projectedLaw FiniteAtomicGeneric.atomicLaw
  apply (integrable_map_measure hcoord.aestronglyMeasurable
    (measurable_of_countable z).aemeasurable).mpr
  exact Integrable.of_finite

/-- The actual expected simplex volume equals (d+1) times the weighted
absolute affine-determinant sum over (d+1)-element subsets. -/
theorem projectedLaw_expectedSimplexVolume {N d : Nat} (q : Fin N -> Real)
    (z : Fin N -> Paper.Point d) (hq : forall i, 0 <= q i) :
    Paper.expectedSimplexVolume (projectedLaw q z) =
      ((d + 1 : Nat) : Real) *
        Bernoulli.finiteD q (Bernoulli.subsetAffineDet z) d := by
  have h := EndpointAssembly.expected_volume_normalization (projectedLaw q z)
  have hF : StronglyMeasurable
      (fun x : Fin (d + 1) -> Paper.Point d => |Geometry.affineDet x|) := by
    simpa only [Function.comp_def] using
      (continuous_abs.comp EndpointAssembly.affineDet_continuous).stronglyMeasurable
  rw [projectedLaw, FiniteAtomicGeneric.iid_atomicLaw_integral q hq z
    (fun x : Fin (d + 1) -> Paper.Point d => |Geometry.affineDet x|) hF] at h
  change (d.factorial : Real) * Paper.expectedSimplexVolume (projectedLaw q z) =
    Sampling.finiteExpectation q
      (fun f : Fin (d + 1) -> Fin N => |Geometry.affineDet (fun i => z (f i))|) at h
  rw [Sampling.finite_affineDet_normalization] at h
  have hfac : Not ((d.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero d
  apply (mul_right_inj' hfac).mp
  calc
    (d.factorial : Real) * Paper.expectedSimplexVolume (projectedLaw q z) =
        ((d + 1).factorial : Real) *
          Bernoulli.finiteD q (Bernoulli.subsetAffineDet z) d := h
    _ = (d.factorial : Real) * (((d + 1 : Nat) : Real) *
          Bernoulli.finiteD q (Bernoulli.subsetAffineDet z) d) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      ring

/-- A coordinate gap is an explicit weighted sum over ordered pairs. -/
theorem projectedLaw_coordinateGap {N d : Nat} (q : Fin N -> Real)
    (z : Fin N -> Paper.Point d) (hq : forall i, 0 <= q i) (j : Fin d) :
    Paper.coordinateGap (projectedLaw q z) j =
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun k => q i * q k * |z i j - z k j|)) := by
  have hF : StronglyMeasurable
      (fun xx : Prod (Paper.Point d) (Paper.Point d) => |xx.1 j - xx.2 j|) :=
    (continuous_abs.comp
      (((continuous_apply j).comp continuous_fst).sub
        ((continuous_apply j).comp continuous_snd))).stronglyMeasurable
  unfold Paper.coordinateGap projectedLaw
  exact FiniteAtomicGeneric.pair_atomicLaw_integral q hq z _ hF

/-- Finite affine-determinant inequality with all probabilistic assumptions
discharged. The factors of 2 use ordered pairs on the right. -/
theorem finite_determinant_bound {N d : Nat} (hd : 1 <= d)
    (q : Fin N -> Real) (z : Fin N -> Paper.Point d)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1) :
    Bernoulli.finiteD q (Bernoulli.subsetAffineDet z) d <=
      (1 / (2 : Real) ^ d) * Finset.prod Finset.univ (fun j =>
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun k => q i * q k * |z i j - z k j|))) := by
  let _ := projectedLaw_probability q z hq hqsum
  have h := Main.random_simplex d hd (projectedLaw q z)
    (projectedLaw_first_moments q z)
  rw [projectedLaw_expectedSimplexVolume q z hq] at h
  simp_rw [projectedLaw_coordinateGap q z hq] at h
  have hpos : (0 : Real) < ((d + 1 : Nat) : Real) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  convert h using 1
  ring

/-- The positive last-coordinate masses used to normalize a zonotope. -/
def totalHeight {N : Nat} (b : Fin N -> Real) : Real :=
  Finset.sum Finset.univ b

def normalizedMass {N : Nat} (b : Fin N -> Real) (i : Fin N) : Real :=
  b i / totalHeight b

def projectedPoint {N d : Nat} (a : Fin N -> Paper.Point d)
    (b : Fin N -> Real) (i : Fin N) : Paper.Point d :=
  fun j => a i j / b i

theorem normalizedMass_nonneg {N : Nat} (b : Fin N -> Real)
    (hb : forall i, 0 <= b i) (i : Fin N) : 0 <= normalizedMass b i := by
  apply div_nonneg (hb i)
  exact Finset.sum_nonneg (fun i _ => hb i)

theorem normalizedMass_sum {N : Nat} (b : Fin N -> Real)
    (hH : Not (totalHeight b = 0)) :
    Finset.sum Finset.univ (normalizedMass b) = 1 := by
  change Finset.sum Finset.univ (fun i => b i / totalHeight b) = 1
  rw [<- Finset.sum_div]
  exact div_self hH

theorem totalHeight_pos {N : Nat} (hN : 0 < N) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) : 0 < totalHeight b := by
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (hb i)
  · exact Exists.intro (Fin.mk 0 hN) (And.intro (Finset.mem_univ _) (hb _))

/-- The planar determinant normalization for an individual pair of
generators. This is an algebraic identity, including coincident projected
points and vanishing planar determinants. -/
theorem normalized_pair {N d : Nat}
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hH : Not (totalHeight b = 0)) (i k : Fin N) (j : Fin d)
    (hi : 0 < b i) (hk : 0 < b k) :
    normalizedMass b i * normalizedMass b k *
        |projectedPoint a b i j - projectedPoint a b k j| =
      |a i j * b k - a k j * b i| / totalHeight b ^ 2 := by
  have hi0 : Not (b i = 0) := ne_of_gt hi
  have hk0 : Not (b k = 0) := ne_of_gt hk
  have hquot : a i j / b i - a k j / b k =
      (a i j * b k - a k j * b i) / (b i * b k) := by
    field_simp [hi0, hk0]
  simp only [normalizedMass, projectedPoint, hquot, abs_div,
    abs_of_pos (mul_pos hi hk)]
  field_simp [hH, hi0, hk0]

/-- The actual coordinate gap of the normalized law is the ordered planar
determinant sum divided by the square of total height. -/
theorem normalized_generator_gap {N d : Nat}
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) (hH : Not (totalHeight b = 0)) (j : Fin d) :
    Paper.coordinateGap
        (projectedLaw (normalizedMass b) (projectedPoint a b)) j =
      (Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun k => |a i j * b k - a k j * b i|))) / totalHeight b ^ 2 := by
  rw [projectedLaw_coordinateGap _ _ (normalizedMass_nonneg b (fun i => le_of_lt (hb i)))]
  simp_rw [normalized_pair a b hH _ _ j (hb _) (hb _)]
  simp_rw [Finset.sum_div]

/-- Row scaling for an ordered tuple of actual generators (a_i,b_i).
Repeated labels and singular tuples are included in the determinant identity. -/
theorem generator_tuple_determinant {N d : Nat}
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, Not (b i = 0)) (f : Fin (d + 1) -> Fin N) :
    Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i))) =
      (Finset.prod Finset.univ (fun i => b (f i))) *
        Geometry.affineDet (fun i => projectedPoint a b (f i)) := by
  change (Matrix.of (fun i j => Fin.lastCases (b (f i)) (a (f i)) j)).det =
    (Finset.prod Finset.univ (fun i => b (f i))) *
      (Matrix.of (fun i j => Fin.lastCases 1 (projectedPoint a b (f i)) j)).det
  rw [<- Matrix.det_mul_column]
  congr 1
  funext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp only [Matrix.of_apply, Fin.lastCases_castSucc, projectedPoint]
    field_simp [hb (f i)]

/-- The factor H^(-(d+1)) in the full determinant normalization, before
enumeration of unordered subsets. -/
theorem normalized_tuple {N d : Nat}
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) (f : Fin (d + 1) -> Fin N) :
    (Finset.prod Finset.univ (fun i => normalizedMass b (f i))) *
        |Geometry.affineDet (fun i => projectedPoint a b (f i))| =
      |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))| /
        totalHeight b ^ (d + 1) := by
  rw [generator_tuple_determinant a b (fun i => ne_of_gt (hb i)) f, abs_mul,
    abs_of_pos (Finset.prod_pos (fun i _ => hb (f i)))]
  simp only [normalizedMass, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- Exact conversion between the normalized affine-determinant sum and the
absolute determinants of actual generator tuples. This is still a determinant
identity, not the missing zonotope-volume theorem. -/
theorem normalized_generator_determinants {N d : Nat}
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) :
    ((d + 1).factorial : Real) *
        Bernoulli.finiteD (normalizedMass b)
          (Bernoulli.subsetAffineDet (projectedPoint a b)) d =
      (Finset.sum Finset.univ (fun f : Fin (d + 1) -> Fin N =>
        |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))|)) /
          totalHeight b ^ (d + 1) := by
  rw [<- Sampling.finite_affineDet_normalization]
  unfold Sampling.finiteExpectation
  simp_rw [normalized_tuple a b hb]
  exact (Finset.sum_div _ _ _).symm

/-- Application to the normalized projected law of a generator family.
The hypothesis on total height records the exclusion of the empty/zero
family, which is handled separately in the geometric corollary. -/
theorem normalized_generator_bound {N d : Nat} (hd : 1 <= d)
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 <= b i) (hH : Not (totalHeight b = 0)) :
    Bernoulli.finiteD (normalizedMass b)
        (Bernoulli.subsetAffineDet (projectedPoint a b)) d <=
      (1 / (2 : Real) ^ d) * Finset.prod Finset.univ (fun j =>
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun k => normalizedMass b i * normalizedMass b k *
            |projectedPoint a b i j - projectedPoint a b k j|))) := by
  exact finite_determinant_bound hd _ _
    (normalizedMass_nonneg b hb) (normalizedMass_sum b hH)

/-- An inequality entirely in determinants of the actual generator family.
The full tuple sum includes repeated labels, whose determinants vanish.
The planar sums are ordered, accounting for the factor 2^d on the right.
The remaining geometric interface is the identification of these sums with
zonotope and projected-zonotope volumes. -/
theorem generator_determinant_bound {N d : Nat} (hd : 1 <= d)
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) (hH : Not (totalHeight b = 0)) :
    ((Finset.sum Finset.univ (fun f : Fin (d + 1) -> Fin N =>
        |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))|)) /
          totalHeight b ^ (d + 1)) / ((d + 1).factorial : Real) <=
      (1 / (2 : Real) ^ d) * Finset.prod Finset.univ (fun j =>
        (Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun k => |a i j * b k - a k j * b i|))) / totalHeight b ^ 2) := by
  rw [<- normalized_generator_determinants a b hb]
  have hfac : Not (((d + 1).factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (d + 1)
  rw [mul_div_cancel_left₀ _ hfac]
  have h := normalized_generator_bound hd a b (fun i => le_of_lt (hb i)) hH
  simp_rw [normalized_pair a b hH _ _ _ (hb _) (hb _)] at h
  simp_rw [<- Finset.sum_div] at h
  exact h

/-- The homogeneous determinant inequality for an actual generator family
with positive last coordinates. All scales, factorials, and ordered-pair
factors have been eliminated. The only remaining interface with Corollary
10.1 is geometric: interpreting these determinant sums as volumes. -/
theorem positive_generators_determinant_inequality {N d : Nat} (hd : 1 <= d)
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 < b i) (hH : Not (totalHeight b = 0)) :
    ((Finset.sum Finset.univ (fun f : Fin (d + 1) -> Fin N =>
        |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))|)) /
          ((d + 1).factorial : Real)) * totalHeight b ^ (d - 1) <=
      Finset.prod Finset.univ (fun j =>
        (Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun k => |a i j * b k - a k j * b i|))) / 2) := by
  let G : Real := Finset.sum Finset.univ (fun f : Fin (d + 1) -> Fin N =>
    |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))|)
  let P : Fin d -> Real := fun j =>
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun k => |a i j * b k - a k j * b i|))
  have hnorm : (G / totalHeight b ^ (d + 1)) / ((d + 1).factorial : Real) <=
      Finset.prod Finset.univ (fun j => (P j / totalHeight b ^ 2) / 2) := by
    have h := generator_determinant_bound hd a b hb hH
    change G / totalHeight b ^ (d + 1) / ((d + 1).factorial : Real) <=
      (1 / (2 : Real) ^ d) *
        Finset.prod Finset.univ (fun j => P j / totalHeight b ^ 2) at h
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    convert h using 1
    ring
  have hHnonneg : 0 <= totalHeight b :=
    Finset.sum_nonneg (fun i _ => le_of_lt (hb i))
  have hscaled := Cor101.homogeneous_projection_bound d hd (totalHeight b) _ _ hHnonneg hnorm
  have hfac : Not (((d + 1).factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (d + 1)
  have hleft : totalHeight b ^ (d + 1) *
      (G / totalHeight b ^ (d + 1) / ((d + 1).factorial : Real)) =
        G / ((d + 1).factorial : Real) := by
    field_simp [hH, hfac]
  have hright (j : Fin d) : totalHeight b ^ 2 *
      (P j / totalHeight b ^ 2 / 2) = P j / 2 := by
    field_simp [hH]
  rw [hleft] at hscaled
  simp_rw [hright] at hscaled
  exact hscaled

/-- Normalized full determinant sum. This definition does not redefine
geometric volume; its equality with zonotope volume is a separate theorem. -/
def fullDeterminantSum {N d : Nat} (a : Fin N -> Paper.Point d)
    (b : Fin N -> Real) : Real :=
  (Finset.sum Finset.univ (fun f : Fin (d + 1) -> Fin N =>
    |Matrix.det (fun i => Fin.lastCases (b (f i)) (a (f i)))|)) /
      ((d + 1).factorial : Real)

/-- Normalized ordered pair determinant sum for one coordinate plane. -/
def planarDeterminantSum {N d : Nat} (a : Fin N -> Paper.Point d)
    (b : Fin N -> Real) (j : Fin d) : Real :=
  (Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
    (fun k => |a i j * b k - a k j * b i|))) / 2

theorem continuous_fullDeterminantSum {N d : Nat}
    (a : Fin N -> Paper.Point d) : Continuous (fullDeterminantSum a) := by
  unfold fullDeterminantSum
  apply Continuous.div_const
  apply continuous_finsetSum
  intro f _
  apply Continuous.abs
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [Fin.lastCases_last] using (continuous_apply (f i))
  · simp only [Fin.lastCases_castSucc]
    exact continuous_const

theorem continuous_planarDeterminantSum {N d : Nat}
    (a : Fin N -> Paper.Point d) (j : Fin d) :
    Continuous (fun b => planarDeterminantSum a b j) := by
  unfold planarDeterminantSum
  fun_prop

/-- Horizontal and zero generators are included by a finite-dimensional
limit of determinant sums, not by assuming continuity of geometric volume. -/
theorem nonnegative_generators_determinant_inequality {N d : Nat} (hd : 1 <= d)
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real)
    (hb : forall i, 0 <= b i) :
    fullDeterminantSum a b * totalHeight b ^ (d - 1) <=
      Finset.prod Finset.univ (planarDeterminantSum a b) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    simp [fullDeterminantSum, planarDeterminantSum, totalHeight]
    apply Finset.prod_nonneg
    intro j _
    unfold planarDeterminantSum
    positivity
  · let bseq : Nat -> Fin N -> Real := fun n i => b i + 1 / ((n : Real) + 1)
    have hbseq (n : Nat) (i : Fin N) : 0 < bseq n i := by
      dsimp only [bseq]
      exact add_pos_of_nonneg_of_pos (hb i) (by positivity)
    have htend : Filter.Tendsto bseq Filter.atTop (nhds b) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simpa only [add_zero, bseq] using
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : Nat => b i + 1 / ((n : Real) + 1))
            Filter.atTop (nhds (b i + 0)))
    have hleft : Continuous (fun c : Fin N -> Real =>
        fullDeterminantSum a c * totalHeight c ^ (d - 1)) := by
      apply (continuous_fullDeterminantSum a).mul
      unfold totalHeight
      fun_prop
    have hright : Continuous (fun c : Fin N -> Real =>
        Finset.prod Finset.univ (planarDeterminantSum a c)) := by
      apply continuous_finsetProd
      intro j _
      exact continuous_planarDeterminantSum a j
    apply le_of_tendsto_of_tendsto
      (hleft.continuousAt.tendsto.comp htend)
      (hright.continuousAt.tendsto.comp htend)
    apply Filter.Eventually.of_forall
    intro n
    exact positive_generators_determinant_inequality hd a (bseq n) (hbseq n)
      (ne_of_gt (totalHeight_pos hN (bseq n) (hbseq n)))

/-- Reversing any generator preserves the absolute full determinant sum. -/
theorem fullDeterminantSum_signs {N d : Nat}
    (a : Fin N -> Paper.Point d) (b s : Fin N -> Real)
    (hs : forall i, |s i| = 1) :
    fullDeterminantSum (fun i j => s i * a i j) (fun i => s i * b i) =
      fullDeterminantSum a b := by
  unfold fullDeterminantSum
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  change |(Matrix.of (fun (i j : Fin (d + 1)) =>
      (Fin.lastCases (s (f i) * b (f i)) (fun j => s (f i) * a (f i) j) j : Real))).det| =
    |(Matrix.of (fun (i j : Fin (d + 1)) =>
      (Fin.lastCases (b (f i)) (a (f i)) j : Real))).det|
  have hmatrix :
      Matrix.of (fun (i j : Fin (d + 1)) =>
        (Fin.lastCases (s (f i) * b (f i)) (fun j => s (f i) * a (f i) j) j : Real)) =
      Matrix.of (fun (i j : Fin (d + 1)) => s (f i) * Fin.lastCases (b (f i)) (a (f i)) j) := by
    ext i j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  have hdet := Matrix.det_mul_column (fun i => s (f i))
    (Matrix.of (fun (i j : Fin (d + 1)) =>
      (Fin.lastCases (b (f i)) (a (f i)) j : Real)))
  simp only [Matrix.of_apply] at hdet
  rw [hmatrix, hdet, abs_mul, Finset.abs_prod]
  simp [hs]

/-- Reversing generators also preserves each absolute planar determinant. -/
theorem planarDeterminantSum_signs {N d : Nat}
    (a : Fin N -> Paper.Point d) (b s : Fin N -> Real)
    (hs : forall i, |s i| = 1) (j : Fin d) :
    planarDeterminantSum (fun i j => s i * a i j) (fun i => s i * b i) j =
      planarDeterminantSum a b j := by
  unfold planarDeterminantSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have h : s i * a i j * (s k * b k) - s k * a k j * (s i * b i) =
      (s i * s k) * (a i j * b k - a k j * b i) := by ring
  rw [h, abs_mul, abs_mul, hs i, hs k, one_mul, one_mul]

/-- Full finite-generator determinant inequality, with no sign or
nondegeneracy assumptions. Horizontal generators, repeated generators,
the empty family, and all lower-dimensional configurations are included.

This is the finite algebraic core of Corollary 10.1. It is not yet its
geometric statement: the determinant sums still require proved bridges to
the actual projected volumes of arbitrary zonotopes. -/
theorem all_generators_determinant_inequality {N d : Nat} (hd : 1 <= d)
    (a : Fin N -> Paper.Point d) (b : Fin N -> Real) :
    fullDeterminantSum a b *
        (Finset.sum Finset.univ (fun i => |b i|)) ^ (d - 1) <=
      Finset.prod Finset.univ (planarDeterminantSum a b) := by
  let s : Fin N -> Real := fun i => if 0 <= b i then 1 else -1
  have hs (i : Fin N) : |s i| = 1 := by
    dsimp only [s]
    split_ifs <;> norm_num
  have hbabs (i : Fin N) : s i * b i = |b i| := by
    dsimp only [s]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  have h := nonnegative_generators_determinant_inequality hd
    (fun i j => s i * a i j) (fun i => s i * b i)
    (fun i => by rw [hbabs]; exact abs_nonneg _)
  rw [fullDeterminantSum_signs a b s hs] at h
  have hplane : planarDeterminantSum (fun i j => s i * a i j) (fun i => s i * b i) =
      planarDeterminantSum a b := funext (planarDeterminantSum_signs a b s hs)
  rw [hplane] at h
  simpa only [totalHeight, hbabs] using h

end Cor101.FiniteBridge
