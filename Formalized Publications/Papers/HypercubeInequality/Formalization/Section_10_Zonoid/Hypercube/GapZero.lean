import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume

/- The zero-gap endpoint follows from actual pair integrability, an a.e.
constant coordinate, and pointwise zero geometric simplex volume. -/

noncomputable section

namespace Hypercube.GapZero

open MeasureTheory

theorem coordinateGap_zero_implies_ae_constant {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (j : Fin d)
    (hgap : Paper.coordinateGap nu j = 0) :
    Exists (fun a : Real => Filter.Eventually (fun z => z j = a) (ae nu)) := by
  have hid : Integrable (fun z : Paper.Point d => z j) nu := by
    apply (integrable_norm_iff (measurable_pi_apply j).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hfirst j
  have hpair : Integrable (fun z : Prod (Paper.Point d) (Paper.Point d) =>
      |z.1 j - z.2 j|) (nu.prod nu) := ((hid.comp_fst nu).sub (hid.comp_snd nu)).abs
  have hzero := (integral_eq_zero_iff_of_nonneg
    (fun z : Prod (Paper.Point d) (Paper.Point d) => abs_nonneg (z.1 j - z.2 j)) hpair).mp hgap
  have hrows := Measure.ae_ae_of_ae_prod hzero
  cases hrows.exists with
  | intro x hx =>
      exact Exists.intro (x j) (hx.mono (fun y hy =>
        (sub_eq_zero.mp (abs_eq_zero.mp hy)).symm))

theorem affineDet_zero_of_constant_coordinate {d : Nat}
    (w : Fin (d + 1) -> Geometry.Point d) (j : Fin d) (a : Real)
    (hw : forall i, w i j = a) : Geometry.affineDet w = 0 := by
  classical
  let M := Geometry.affineMatrix w
  let c : Fin (d + 1) -> Real := fun k => if k = Fin.last d then a else 0
  have hcol (r : Fin (d + 1)) :
      Finset.sum Finset.univ (fun k => c k * M r k) = M r j.castSucc := by
    simp [c, M, Geometry.affineMatrix, hw r]
  have heq : (fun r => Finset.sum Finset.univ (fun k => c k * M r k)) =
      (fun r => M r j.castSucc) := funext hcol
  have hd := Matrix.det_updateCol_sum M j.castSucc c
  simp only [smul_eq_mul] at hd
  rw [heq, Matrix.updateCol_eq_self] at hd
  simpa [c, M, Geometry.affineDet] using hd

theorem simplexVolume_zero_of_constant_coordinate {d : Nat}
    (w : Fin (d + 1) -> Paper.Point d) (j : Fin d) (a : Real)
    (hw : forall i, w i j = a) : Paper.simplexVolume w = 0 := by
  have hvolume := Geometry.simplex_volume_factorial w
  rw [affineDet_zero_of_constant_coordinate w j a hw, abs_zero] at hvolume
  have hpos : Not ((Nat.factorial d : Real) = 0) := by positivity
  exact (mul_eq_zero.mp hvolume).resolve_left hpos

theorem expectedSimplexVolume_zero_of_ae_constant_coordinate {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (j : Fin d) (a : Real)
    (hconstant : Filter.Eventually (fun z => z j = a) (ae nu)) :
    Paper.expectedSimplexVolume nu = 0 := by
  have hall : Filter.Eventually
      (fun w : Fin (d + 1) -> Paper.Point d => forall i, w i j = a)
      (ae (Measure.pi (fun _ : Fin (d + 1) => nu))) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin (d + 1) => nu) i).quasiMeasurePreserving.ae hconstant
  have hzero : Filter.Eventually
      (fun w : Fin (d + 1) -> Paper.Point d => Paper.simplexVolume w = 0)
      (ae (Measure.pi (fun _ : Fin (d + 1) => nu))) :=
    hall.mono (fun w hw => simplexVolume_zero_of_constant_coordinate w j a hw)
  unfold Paper.expectedSimplexVolume
  rw [integral_congr_ae hzero]
  exact integral_zero _ _

theorem expectedSimplexVolume_zero_of_coordinateGap_zero {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (j : Fin d)
    (hgap : Paper.coordinateGap nu j = 0) : Paper.expectedSimplexVolume nu = 0 := by
  cases coordinateGap_zero_implies_ae_constant nu hfirst j hgap with
  | intro a ha => exact expectedSimplexVolume_zero_of_ae_constant_coordinate nu j a ha

end Hypercube.GapZero
