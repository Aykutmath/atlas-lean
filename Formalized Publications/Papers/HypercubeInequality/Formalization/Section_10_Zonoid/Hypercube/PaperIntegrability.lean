import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Mathlib.MeasureTheory.Integral.Prod

/-!
Governance for the real-integral paper definitions.
Under the exact source coordinate first moments, those integrals are genuine
finite expectations. Their meanings do not rely on Mathlib's nonintegrable
real-integral fallback. This module adds no stronger moment assumption.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.PaperIntegrability

private theorem affineDet_continuous (d : Nat) :
    Continuous (fun z : Fin (d + 1) -> Geometry.Point d => Geometry.affineDet z) := by
  unfold Geometry.affineDet
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin (d + 1) -> Geometry.Point d => (1 : Real)))
  next j =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_castSucc, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i))

theorem affineDet_abs_integrable {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Fin (d + 1) -> Paper.Point d => |Geometry.affineDet z|)
      (Measure.pi (fun _ : Fin (d + 1) => nu)) := by
  have hrow : Integrable (fun z => Moments.rowFactor z) nu :=
    (integrable_const (1 : Real)).add
      (integrable_finsetSum Finset.univ (fun j _ => hfirst j))
  have hdom := (Integrable.fintype_prod (fun _ : Fin (d + 1) => hrow)).const_mul
    (Nat.factorial (d + 1) : Real)
  have hdetmeas : Measurable
      (fun z : Fin (d + 1) -> Paper.Point d => |Geometry.affineDet z|) :=
    ((affineDet_continuous d).abs).measurable
  apply hdom.mono_nonneg hdetmeas.aestronglyMeasurable
  next => exact Filter.Eventually.of_forall (fun z => abs_nonneg (Geometry.affineDet z))
  next => exact Filter.Eventually.of_forall (Moments.affineDet_abs_bound)

theorem simplexVolume_integrable {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Fin (d + 1) -> Paper.Point d => Paper.simplexVolume z)
      (Measure.pi (fun _ : Fin (d + 1) => nu)) := by
  have heq : (fun z : Fin (d + 1) -> Paper.Point d => Paper.simplexVolume z) =
      (fun z => |Geometry.affineDet z| / (Nat.factorial d : Real)) := by
    funext z
    have hfactor := Geometry.simplex_volume_factorial z
    have hpos : (0 : Real) < (Nat.factorial d : Real) := by
      exact_mod_cast Nat.factorial_pos d
    change Geometry.simplexVolume z = _
    apply (eq_div_iff hpos.ne').mpr
    nlinarith
  rw [heq]
  exact (affineDet_abs_integrable nu hfirst).div_const (Nat.factorial d : Real)

theorem coordinateGap_integrable {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (j : Fin d) :
    Integrable (fun zz : Prod (Paper.Point d) (Paper.Point d) => |zz.1 j - zz.2 j|)
      (nu.prod nu) := by
  have hdom := ((hfirst j).comp_fst nu).add ((hfirst j).comp_snd nu)
  have hmeas : Measurable
      (fun zz : Prod (Paper.Point d) (Paper.Point d) => |zz.1 j - zz.2 j|) :=
    ((continuous_abs.comp
      (((continuous_apply j).comp continuous_fst).sub
        ((continuous_apply j).comp continuous_snd)))).measurable
  apply hdom.mono_nonneg hmeas.aestronglyMeasurable
  next => exact Filter.Eventually.of_forall (fun zz => abs_nonneg (zz.1 j - zz.2 j))
  next => exact Filter.Eventually.of_forall (fun zz => abs_sub (zz.1 j) (zz.2 j))

end Hypercube.PaperIntegrability
