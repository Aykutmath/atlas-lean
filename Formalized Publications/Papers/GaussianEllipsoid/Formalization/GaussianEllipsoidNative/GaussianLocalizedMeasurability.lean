import GaussianLocalizedProbability

noncomputable section
open GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped BigOperators

namespace GaussianEllipsoid.Localized

/-- Fixed-coefficient Gaussian observations depend continuously on all drivers. -/
theorem continuous_bilinearFlat (r n : ℕ) (z : Fin n → ℝ) :
    Continuous (bilinearFlat r n z) := by
  let f : BilinearSample r n → (Fin r × Fin r → ℝ) :=
    fun p ab => (Real.sqrt (r:ℝ))⁻¹ * ∑ i, z i*p.1 i ab.1*p.2 (i,ab.2)
  have hf : Continuous f := by
    apply continuous_pi
    intro ab
    unfold f
    fun_prop
  have hm := (PiLp.continuous_toLp 2 (fun _ : Fin r × Fin r => ℝ)).comp hf
  have heq : bilinearFlat r n z = (WithLp.equiv 2 (Fin r × Fin r → ℝ)).symm ∘ f := by
    funext p
    ext ab
    exact matrixCLM_bilinearDriver_apply _ z p.1 p.2 ab.1 ab.2
  rw [heq]
  exact hm

theorem continuous_localizedOperator_eval (d : ℝ) (r n : ℕ) (z : Coeff n) :
    Continuous (fun p => localizedOperator d r n p z) := by
  have hc : Continuous (bilinearFrobenius r n z) :=
    (frobeniusEquivEuclidean r r).symm.continuous.comp (continuous_bilinearFlat r n z)
  exact hc.const_smul (Real.sqrt (r:ℝ)/Real.sqrt d)

/-- Existential choice of coefficients after observing data still yields an
open event: every fixed strict bad inequality is open. -/
theorem isOpen_homogeneousBad (d : ℝ) (r n : ℕ) (A β B K c : ℝ) :
    IsOpen (homogeneousBad (localizedOperator d r n) A β B K c d) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hbad⟩
  have hopen : IsOpen {p : BilinearSample r n |
      spectralNuclearNorm (localizedOperator d r n p (U+V)) < c*q*d} :=
    isOpen_lt ((continuous_spectralNuclear r r).comp
      (continuous_localizedOperator_eval d r n (U+V))) continuous_const
  apply Filter.mem_of_superset (hopen.mem_nhds hbad)
  intro p' hp'
  exact ⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hp'⟩

/-- The Frobenius control event is closed, as an intersection over all
coefficient vectors of closed inequalities. -/
theorem isClosed_frobeniusContinuity (d : ℝ) (r n : ℕ) (L : ℝ) :
    IsClosed (frobeniusContinuity (localizedOperator d r n) L d) := by
  unfold frobeniusContinuity
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  exact isClosed_le (continuous_localizedOperator_eval d r n x).norm continuous_const

/-- Thus the localized estimate is an ordinary probability bound as well as
an outer-measure bound; no measurability of a chosen minimizing pair is used. -/
theorem measurableSet_localized_event (d : ℝ) (r n : ℕ) (A β B K c L : ℝ) :
    MeasurableSet (homogeneousBad (localizedOperator d r n) A β B K c d ∩
      frobeniusContinuity (localizedOperator d r n) L d) :=
  (isOpen_homogeneousBad d r n A β B K c).measurableSet.inter
    (isClosed_frobeniusContinuity d r n L).measurableSet

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.measurableSet_localized_event
