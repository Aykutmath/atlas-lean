import BilinearLawTransport
import MultiscaleBlocks
import Mathlib.Probability.Independence.Basic

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianBilinearTransport GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped ENNReal
namespace GaussianPairedBlocks

/-- Consecutive r-coordinate blocks fit exactly into an h-coordinate array. -/
def consecutiveBlocks (h r : ℕ) : Fin (h/r) × Fin r ↪ Fin h :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (Nat.div_mul_le_self h r))

/-- Extract a paired coordinate block from the actual two independent Gaussian arrays. -/
def pairedBlock {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h)
    (j : Fin J) (z : GaussianEntries n h × GaussianEntries n h) :
    GaussianEntries n r × GaussianEntries n r :=
  (fun p => z.1 (p.1, eL (j,p.2)), fun p => z.2 (p.1, eR (j,p.2)))

theorem measurable_pairedBlock {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h)
    (j : Fin J) : Measurable (pairedBlock (n:=n) eL eR j) := by
  exact (measurable_pi_iff.mpr fun p => (measurable_pi_apply _).comp measurable_fst).prodMk
    (measurable_pi_iff.mpr fun p => (measurable_pi_apply _).comp measurable_snd)

theorem sideBlocks_preserving {n h J r : ℕ} (e : Fin J × Fin r ↪ Fin h) :
    MeasurePreserving (fun z : GaussianEntries n h => fun j : Fin J =>
      fun p : Fin n × Fin r => z (p.1, e (j,p.2)))
      (gaussianProductLaw (Fin n × Fin h))
      (Measure.pi (fun _ : Fin J => gaussianProductLaw (Fin n × Fin r))) := by
  let t : Fin J × (Fin n × Fin r) → Fin n × Fin h := fun p => (p.2.1,e (p.1,p.2.2))
  have ht : Function.Injective t := by
    intro a b hab
    change (a.2.1, e (a.1,a.2.2)) = (b.2.1, e (b.1,b.2.2)) at hab
    obtain ⟨hn, he⟩ := Prod.mk.inj hab
    obtain ⟨hj, hr⟩ := Prod.mk.inj (e.injective he)
    exact Prod.ext hj (Prod.ext hn hr)
  have h₁ : MeasurePreserving (fun z : GaussianEntries n h => fun p => z (t p))
      (gaussianProductLaw (Fin n × Fin h)) (gaussianProductLaw (Fin J × (Fin n × Fin r))) :=
    ⟨measurable_pi_iff.mpr (fun p => measurable_pi_apply (t p)),
      gaussianProductLaw_map_subfamily t ht⟩
  have h₂ : MeasurePreserving
      (fun z : (Fin J × (Fin n × Fin r)) → ℝ => fun j p => z (j,p))
      (gaussianProductLaw (Fin J × (Fin n × Fin r)))
      (Measure.pi (fun _ : Fin J => gaussianProductLaw (Fin n × Fin r))) :=
    ⟨measurable_pi_iff.mpr (fun j => measurable_pi_iff.mpr (fun p => measurable_pi_apply (j,p))),
      gaussianProductLaw_map_curry⟩
  exact h₂.comp h₁

/-- The joint block law is a genuine product law, not an independence assumption. -/
theorem pairedBlocks_preserving {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h) :
    MeasurePreserving (fun z => fun j => pairedBlock (n:=n) eL eR j z)
      (tensorGaussianLaw n h) (Measure.pi (fun _ : Fin J => tensorGaussianLaw n r)) := by
  have hp := (sideBlocks_preserving (n:=n) eL).prod (sideBlocks_preserving (n:=n) eR)
  have he := (measurePreserving_arrowProdEquivProdArrow (GaussianEntries n r)
    (GaussianEntries n r) (Fin J)
    (fun _ => gaussianProductLaw (Fin n × Fin r))
    (fun _ => gaussianProductLaw (Fin n × Fin r))).symm
  exact he.comp hp

/-- Every paired block has the exact lower-dimensional two-array Gaussian law. -/
theorem pairedBlock_preserving {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h)
    (j : Fin J) : MeasurePreserving (pairedBlock (n:=n) eL eR j)
      (tensorGaussianLaw n h) (tensorGaussianLaw n r) := by
  have hL : Function.Injective (fun p : Fin n × Fin r => (p.1,eL (j,p.2))) := by
    intro a b hab
    obtain ⟨hn, he⟩ := Prod.mk.inj hab
    exact Prod.ext hn (Prod.mk.inj (eL.injective he)).2
  have hR : Function.Injective (fun p : Fin n × Fin r => (p.1,eR (j,p.2))) := by
    intro a b hab
    obtain ⟨hn, he⟩ := Prod.mk.inj hab
    exact Prod.ext hn (Prod.mk.inj (eR.injective he)).2
  have hpL : MeasurePreserving (fun z : GaussianEntries n h => fun p : Fin n × Fin r => z (p.1,eL (j,p.2)))
      (gaussianProductLaw (Fin n × Fin h)) (gaussianProductLaw (Fin n × Fin r)) :=
    ⟨measurable_pi_iff.mpr (fun p => measurable_pi_apply _), gaussianProductLaw_map_subfamily _ hL⟩
  have hpR : MeasurePreserving (fun z : GaussianEntries n h => fun p : Fin n × Fin r => z (p.1,eR (j,p.2)))
      (gaussianProductLaw (Fin n × Fin h)) (gaussianProductLaw (Fin n × Fin r)) :=
    ⟨measurable_pi_iff.mpr (fun p => measurable_pi_apply _), gaussianProductLaw_map_subfamily _ hR⟩
  exact hpL.prod hpR

theorem pairedBlocks_iIndepFun {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h) :
    iIndepFun (pairedBlock (n:=n) eL eR) (tensorGaussianLaw n h) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pairedBlock eL eR j).aemeasurable)).mpr
  simpa only [(pairedBlock_preserving eL eR _).map_eq] using
    (pairedBlocks_preserving (n:=n) eL eR).map_eq

/-- Block-local measurable events are independent under the ambient actual law. -/
theorem pairedBlocks_iIndepSet {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h)
    (E : Fin J → Set (GaussianEntries n r × GaussianEntries n r))
    (hE : ∀ j, MeasurableSet (E j)) :
    iIndepSet (fun j => pairedBlock eL eR j ⁻¹' E j) (tensorGaussianLaw n h) := by
  apply (iIndepSet_iff_meas_biInter (fun j => (hE j).preimage
    (measurable_pairedBlock eL eR j))).mpr
  intro s
  exact (pairedBlocks_iIndepFun eL eR).measure_inter_preimage_eq_mul s (fun j _ => hE j)

/-- Actual-law block amplification for arbitrary measurable block events. -/
theorem measure_many_paired_bad {n h J r : ℕ} (eL eR : Fin J × Fin r ↪ Fin h)
    (E : Fin J → Set (GaussianEntries n r × GaussianEntries n r))
    (hE : ∀ j, MeasurableSet (E j)) (p : ℝ≥0∞)
    (hp : ∀ j, tensorGaussianLaw n r (E j) ≤ p) (m : ℕ) :
    tensorGaussianLaw n h
      {z | m ≤ GaussianEllipsoidCandidate.badCount (fun j => pairedBlock eL eR j ⁻¹' E j) z}
      ≤ (2 : ℝ≥0∞)^J * p^m := by
  have hmarg : ∀ j, tensorGaussianLaw n h (pairedBlock eL eR j ⁻¹' E j) ≤ p := by
    intro j
    have heq := (pairedBlock_preserving (n:=n) eL eR j).map_eq
    have hh := hp j
    rw [← heq, Measure.map_apply (measurable_pairedBlock eL eR j) (hE j)] at hh
    exact hh
  simpa only [Fintype.card_fin] using
    GaussianEllipsoidCandidate.measure_many_independent_bad_two_pow _ _
      (pairedBlocks_iIndepSet eL eR E hE) p hmarg m

end GaussianPairedBlocks
