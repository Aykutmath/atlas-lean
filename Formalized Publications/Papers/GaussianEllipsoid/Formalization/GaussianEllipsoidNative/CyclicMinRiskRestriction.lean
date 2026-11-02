import FiniteEventAveraging
import BMPhysicalAllR

noncomputable section
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoidFinalPassage BMBoxRiskAssembly
open scoped BigOperators

namespace BMCyclicRiskRestriction

local instance {d n : ℕ} : IsProbabilityMeasure (coordinateSampleLaw d n) := by
  unfold coordinateSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianProductLaw (Fin d)) := fun _ => inferInstance
  letI : ∀ _i : Fin n, SigmaFinite (gaussianProductLaw (Fin d)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

/-- Literal cyclic restriction in the original ordinary Gaussian coordinates. -/
def coordinateCyclicRows {d n N : ℕ} [NeZero N] (h : n ≤ N) (j : Fin N)
    (X : CoordinateSample d N) : CoordinateSample d n :=
  fun i => X ((prefixEmbedding h) i+j)

/-- Every cyclic window has exactly the actual smaller iid Gaussian law. -/
theorem coordinateCyclicRows_preserving {d n N : ℕ} [NeZero N]
    (h : n ≤ N) (j : Fin N) :
    MeasurePreserving (coordinateCyclicRows (d := d) h j)
      (coordinateSampleLaw d N) (coordinateSampleLaw d n) := by
  have hlarge := sampleEuclideanEquiv_measurePreserving d N
  have hsmall := (sampleEuclideanEquiv_measurePreserving d n).symm
  have hrow := cyclicRows_preserving (d := d) h j
  convert! hsmall.comp (hrow.comp hlarge) using 1

/-- Exact risk expression in a cyclic window. -/
theorem fittingRisk_cyclic {d n N : ℕ} [NeZero N] (h : n ≤ N) (j : Fin N)
    (r : ℝ) (S : BMRescaling.Square d) (X : CoordinateSample d N) :
    fittingRisk r S (coordinateCyclicRows h j X) =
      (∑ i : Fin n, |BMRescaling.fittingResidual S (X ((prefixEmbedding h) i+j))|^r)/(n:ℝ) := by
  unfold fittingRisk empiricalPower coordinateCyclicRows
  ring

/-- The fraction of cyclic windows with large minimized risk is controlled by
the full minimized risk itself. The proof takes the infimum after proving the
cyclic averaging inequality for every candidate, requiring no minimizer,
attainment, choice of a sample-dependent witness, or measurable selector. -/
theorem bad_cyclic_minRisk_fraction_le {d n N : ℕ} [NeZero N]
    (hn : 0 < n) (hdom : n ≤ N) (X : CoordinateSample d N)
    {lo hi r ε : ℝ} (hlohi : lo ≤ hi) (hε : 0 < ε) :
    (∑ j : Fin N, if ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r
      then (1:ℝ) else 0)/(N:ℝ) ≤ minFittingRisk d N X lo hi r/ε := by
  classical
  apply (le_div_iff₀ hε).2
  apply le_csInf
  · exact ⟨_,_,lower_identity_mem_spectralBox d hlohi,rfl⟩
  · rintro t ⟨S,hS,rfl⟩
    let v : Fin N → ℝ := fun j => |BMRescaling.fittingResidual S (X j)|^r
    have hv : ∀ j, 0 ≤ v j := fun j => Real.rpow_nonneg (abs_nonneg _) _
    have hbad (j : Fin N)
        (hj : ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r) :
        ε < (∑ i : Fin n, v ((prefixEmbedding hdom) i+j))/(n:ℝ) := by
      have h := hj.trans_le (minFittingRisk_le (coordinateCyclicRows hdom j X) r hS)
      simpa only [fittingRisk_cyclic,v] using h
    have hfull : (∑ j : Fin N, v j)/(N:ℝ) ≤ fittingRisk r S X := by
      unfold fittingRisk empiricalPower v
      simp only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul]
      exact le_rfl
    have hf := bad_cyclic_fraction_le hn (prefixEmbedding hdom) v hv
      (fun j => ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r)
      ε (fittingRisk r S X) hε hbad hfull
    exact (le_div_iff₀ hε).1 hf

/-- Exact smaller-sample minrisk tail bound under the actual Gaussian laws.
Windows may overlap and are not assumed independent. The additive δ/ε term
comes from finite cyclic averaging, not uniform integrability. -/
theorem minRisk_probability_le {d n N : ℕ}
    (hn : 0 < n) (hdom : n ≤ N) {lo hi r ε δ : ℝ}
    (hlohi : lo ≤ hi) (hr : 0 ≤ r) (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (coordinateSampleLaw d n).real {x | ε < minFittingRisk d n x lo hi r} ≤
      (coordinateSampleLaw d N).real {x | δ < minFittingRisk d N x lo hi r} + δ/ε := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt (hn.trans_le hdom)⟩
  let E : Fin N → Set (CoordinateSample d N) :=
    fun j => {X | ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r}
  let F : Set (CoordinateSample d N) := {X | δ < minFittingRisk d N X lo hi r}
  have hsmall := measurableSet_minRiskR_tail d n lo hi r ε hr
  have hE (j : Fin N) : MeasurableSet (E j) :=
    hsmall.preimage (coordinateCyclicRows_preserving hdom j).measurable
  have hF : MeasurableSet F := measurableSet_minRiskR_tail d N lo hi r δ hr
  have hp (j : Fin N) : (coordinateSampleLaw d N).real (E j) =
      (coordinateSampleLaw d n).real {x | ε < minFittingRisk d n x lo hi r} :=
    (coordinateCyclicRows_preserving hdom j).measureReal_preimage hsmall.nullMeasurableSet
  have hpoint (X : CoordinateSample d N) :
      (∑ j : Fin N, (E j).indicator (fun _ => (1:ℝ)) X)/(N:ℝ) ≤
        δ/ε+F.indicator (fun _ => (1:ℝ)) X := by
    have hid : (∑ j : Fin N, (E j).indicator (fun _ => (1:ℝ)) X) =
        ∑ j : Fin N, if ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r
          then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Set.indicator_apply,E,Set.mem_setOf_eq]
    rw [hid]
    by_cases hX : X ∈ F
    · rw [Set.indicator_of_mem hX]
      have hfrac : (∑ j : Fin N, if ε < minFittingRisk d n (coordinateCyclicRows hdom j X) lo hi r
          then (1:ℝ) else 0)/(N:ℝ) ≤ 1 := by
        apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))).2
        calc
          _ ≤ ∑ _j : Fin N, (1:ℝ) := Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
          _ = _ := by simp
      linarith [div_nonneg hδ hε.le]
    · rw [Set.indicator_of_notMem hX,add_zero]
      have hmin : minFittingRisk d N X lo hi r ≤ δ := le_of_not_gt hX
      exact (bad_cyclic_minRisk_fraction_le hn hdom X hlohi hε).trans
        (div_le_div_of_nonneg_right hmin hε.le)
  have h := probability_le_of_average_indicators (coordinateSampleLaw d N) E F hE hF
    ((coordinateSampleLaw d n).real {x | ε < minFittingRisk d n x lo hi r}) (δ/ε) hp hpoint
  simpa only [add_comm] using h

#print axioms coordinateCyclicRows_preserving
#print axioms bad_cyclic_minRisk_fraction_le
#print axioms minRisk_probability_le
end BMCyclicRiskRestriction
