import PaperLocalizedHalfDimension

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SmallBall
namespace GaussianEllipsoid.Localized

/-- The paper's existential localized bad event is open even when its
coefficients/support/positive scale are chosen after observing the sample. -/
theorem isOpen_paperLocalizedBad (d : ℝ) (r n : ℕ) (A β B K c θ : ℝ) :
    IsOpen (paperLocalizedBad (localizedOperator d r n) A β B K c d θ) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hbad⟩
  have hopen : IsOpen {p : BilinearSample r n |
      spectralNuclearNorm (localizedOperator d r n p (U+V)) < c*q*d} :=
    isOpen_lt ((continuous_spectralNuclear r r).comp
      (continuous_localizedOperator_eval d r n (U+V))) continuous_const
  apply Filter.mem_of_superset (hopen.mem_nhds hbad)
  intro p' hp'
  exact ⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hp'⟩

theorem measurableSet_paperLocalizedEvent (d : ℝ) (r n : ℕ) (A β B K c θ L : ℝ) :
    MeasurableSet (paperLocalizedBad (localizedOperator d r n) A β B K c d θ ∩
      frobeniusContinuity (localizedOperator d r n) L d) :=
  (isOpen_paperLocalizedBad d r n A β B K c θ).measurableSet.inter
    (isClosed_frobeniusContinuity d r n L).measurableSet
end GaussianEllipsoid.Localized
#print axioms GaussianEllipsoid.Localized.measurableSet_paperLocalizedEvent
