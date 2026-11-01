import Section_10_Zonoid.Hypercube.FiniteAtomic
import Mathlib.Tactic.FinCases

/- Exact source regression: the checkerboard lift of the uniform projected
square. Scalar arithmetic and all finite set equalities are kernel checked. -/

noncomputable section

namespace Hypercube.Regressions

open MeasureTheory

def squarePoints : Fin 4 -> Geometry.Point 2 := ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]
def squareLabels : Fin 4 -> Real := ![1, 0, 0, 1]
def squareMass : Fin 4 -> Real := fun _ => 1 / 4

theorem affineMatrix_dimTwo_zero (w : Fin 3 -> Geometry.Point 2) (i : Fin 3) :
    Geometry.affineMatrix w i 0 = w i 0 := by
  change Fin.lastCases (motive := fun _ : Fin 3 => Real) 1 (w i)
    (Fin.castSucc (0 : Fin 2)) = w i 0
  rw [Fin.lastCases_castSucc]

theorem affineMatrix_dimTwo_one (w : Fin 3 -> Geometry.Point 2) (i : Fin 3) :
    Geometry.affineMatrix w i 1 = w i 1 := by
  change Fin.lastCases (motive := fun _ : Fin 3 => Real) 1 (w i)
    (Fin.castSucc (1 : Fin 2)) = w i 1
  rw [Fin.lastCases_castSucc]

theorem affineMatrix_dimTwo_last (w : Fin 3 -> Geometry.Point 2) (i : Fin 3) :
    Geometry.affineMatrix w i 2 = 1 := by
  change Fin.lastCases (motive := fun _ : Fin 3 => Real) 1 (w i) (Fin.last 2) = 1
  rw [Fin.lastCases_last]

theorem square_univ_enumeration
    (h : (Finset.univ : Finset (Fin 4)).card = 4) :
    (Finset.univ : Finset (Fin 4)).orderEmbOfFin h = (OrderIso.refl (Fin 4)).toOrderEmbedding := by
  exact (Finset.orderEmbOfFin_unique' h (fun i => Finset.mem_univ i)).symm

theorem square_omitted_abs_det (i : Fin 4) :
    |Geometry.affineDet (fun j => squarePoints (i.succAbove j))| = 1 := by
  fin_cases i
  all_goals rw [Geometry.affineDet, Matrix.det_fin_three]
  all_goals norm_num [affineMatrix_dimTwo_zero, affineMatrix_dimTwo_one,
    affineMatrix_dimTwo_last, squarePoints, Fin.succAbove]

theorem square_cofactor (i : Fin 4) :
    Geometry.cofactor squarePoints i = ![-1, 1, 1, -1] i := by
  fin_cases i
  all_goals unfold Geometry.cofactor Geometry.affineDet
  all_goals rw [Matrix.det_fin_three]
  all_goals norm_num [affineMatrix_dimTwo_zero, affineMatrix_dimTwo_one,
    affineMatrix_dimTwo_last, squarePoints, Fin.succAbove]

theorem square_finiteD : Bernoulli.finiteD squareMass
    (Bernoulli.subsetAffineDet squarePoints) 2 = 1 / 16 := by
  have hsets : (Finset.univ : Finset (Fin 4)).powersetCard 3 =
      Finset.univ.image (fun i => (Finset.univ : Finset (Fin 4)).erase i) := by decide
  unfold Bernoulli.finiteD
  rw [hsets, Finset.sum_image (Finset.erase_injOn Finset.univ)]
  have hminor (i : Fin 4) :
      |Bernoulli.subsetAffineDet squarePoints (Finset.univ.erase i)| = 1 := by
    have h := Sampling.subsetAffineDet_erase squarePoints Finset.univ (by decide) i
    rw [square_univ_enumeration] at h
    change Bernoulli.subsetAffineDet squarePoints (Finset.univ.erase i) =
      Geometry.affineDet (fun j => squarePoints (i.succAbove j)) at h
    rw [h]
    exact square_omitted_abs_det i
  have hterm (i : Fin 4) : Finset.prod (Finset.univ.erase i) squareMass *
      |Bernoulli.subsetAffineDet squarePoints (Finset.univ.erase i)| = 1 / 64 := by
    rw [hminor]
    rw [mul_one]
    unfold squareMass
    rw [Finset.prod_const]
    norm_num [Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp_rw [hterm]
  norm_num

theorem square_alternating_abs :
    |BinaryCocycle.increasingAlternatingSum squareLabels
      (Bernoulli.subsetAffineDet squarePoints) Finset.univ| = 2 := by
  rw [Sampling.increasing_sum_eq_cofactor_sum squarePoints squareLabels Finset.univ (by decide),
    square_univ_enumeration]
  change |Finset.sum Finset.univ (fun i : Fin 4 =>
    Geometry.cofactor squarePoints i * squareLabels i)| = 2
  rw [Fin.sum_univ_four]
  norm_num [square_cofactor, squareLabels]

theorem square_finiteL : Bernoulli.finiteL squareMass squareLabels
    (Bernoulli.subsetAffineDet squarePoints) 2 = 1 / 128 := by
  have hsets : (Finset.univ : Finset (Fin 4)).powersetCard 4 = {Finset.univ} := by decide
  unfold Bernoulli.finiteL
  rw [hsets, Finset.sum_singleton, square_alternating_abs]
  norm_num [squareMass, Fin.prod_univ_four]

theorem square_checkerboard_objective :
    integral (Measure.pi (fun _ : Fin 4 => FiniteAtomic.labelMeasure squareMass))
      (fun f => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => squarePoints (f j)) i * squareLabels (f i))|) = 3 / 16 := by
  rw [FiniteAtomic.iid_height_normalization squareMass squareLabels (by intro i; norm_num [squareMass])
    squarePoints, square_finiteL]
  norm_num

theorem square_expected_radonMass :
    integral (Measure.pi (fun _ : Fin 4 => FiniteAtomic.labelMeasure squareMass))
      (fun f => Geometry.radonMass (fun j => squarePoints (f j))) = 3 / 4 := by
  rw [FiniteAtomic.iid_radonMass_normalization squareMass (by intro i; norm_num [squareMass])
    (by norm_num [squareMass, Fin.sum_univ_four]) squarePoints, square_finiteD]
  norm_num

theorem square_checkerboard_mean :
    integral (FiniteAtomic.labelMeasure squareMass) squareLabels = 1 / 2 := by
  rw [FiniteAtomic.label_integral squareMass (by intro i; norm_num [squareMass])]
  norm_num [Fin.sum_univ_four, squareMass, squareLabels]

theorem square_checkerboard_gate_rhs :
    2 * integral (FiniteAtomic.labelMeasure squareMass) squareLabels *
      (1 - integral (FiniteAtomic.labelMeasure squareMass) squareLabels) *
        integral (Measure.pi (fun _ : Fin 4 => FiniteAtomic.labelMeasure squareMass))
          (fun f => Geometry.radonMass (fun j => squarePoints (f j))) = 3 / 8 := by
  rw [square_checkerboard_mean, square_expected_radonMass]
  norm_num

end Hypercube.Regressions
