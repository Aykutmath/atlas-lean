import AHHGaussianLaw

/-! Exact independent-row law of the actual four-real Gaussian construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators
namespace AHHGaussian

abbrev RealRow (h : ℕ) := Fin h → ℝ
abbrev PairRealRow (h : ℕ) := RealRow h × RealRow h
abbrev FourRealRow (h : ℕ) := PairRealRow h × PairRealRow h

def pairRealRowLaw (h : ℕ) : Measure (PairRealRow h) :=
  (gaussianProductLaw (Fin h)).prod (gaussianProductLaw (Fin h))
def fourRealRowLaw (h : ℕ) : Measure (FourRealRow h) :=
  (pairRealRowLaw h).prod (pairRealRowLaw h)

instance pairRealRowLaw_probability (h : ℕ) : IsProbabilityMeasure (pairRealRowLaw h) := by
  unfold pairRealRowLaw
  infer_instance
instance fourRealRowLaw_probability (h : ℕ) : IsProbabilityMeasure (fourRealRowLaw h) := by
  unfold fourRealRowLaw
  infer_instance

/-- Finite product Fubini, written at the scalar-coordinate law. -/
theorem scalarRows_map_uncurry {κ ι : Type*} [Fintype κ] [Fintype ι] :
    Measure.map (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2)
      (Measure.pi (fun _ : κ => gaussianProductLaw ι)) = gaussianProductLaw (κ × ι) := by
  have hm : Measurable (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2) :=
    measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  unfold gaussianProductLaw
  apply (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have heq : (fun g : κ → ι → ℝ => fun p : κ × ι => g p.1 p.2) ⁻¹' Set.univ.pi S =
      Set.univ.pi (fun k : κ => Set.univ.pi (fun i : ι => S (k, i))) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
  rw [heq, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : κ × ι => gaussianReal 0 1 (S p))).symm

theorem scalarEntries_map_curry {κ ι : Type*} [Fintype κ] [Fintype ι] :
    Measure.map (fun z : (κ × ι) → ℝ => fun k i => z (k,i)) (gaussianProductLaw (κ × ι)) =
      Measure.pi (fun _ : κ => gaussianProductLaw ι) := by
  rw [← scalarRows_map_uncurry]
  rw [Measure.map_map]
  · exact Measure.map_id
  · exact measurable_pi_iff.mpr (fun k => measurable_pi_iff.mpr (fun i => measurable_pi_apply (k,i)))
  · exact measurable_pi_iff.mpr (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))

def pairRealRows (n h : ℕ) (x : PairEntries n h) (i : Fin n) : PairRealRow h :=
  (fun j => x.1 (i,j), fun j => x.2 (i,j))

def fourRealRows (n h : ℕ) (x : FourEntries n h) (i : Fin n) : FourRealRow h :=
  (pairRealRows n h x.1 i, pairRealRows n h x.2 i)

theorem pairRealRows_preserving (n h : ℕ) :
    MeasurePreserving (pairRealRows n h) (pairGaussianLaw n h)
      (Measure.pi (fun _ : Fin n => pairRealRowLaw h)) := by
  have hc : MeasurePreserving (fun x : Entries n h => fun i j => x (i,j))
      (gaussianProductLaw (Fin n × Fin h))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin h))) :=
    ⟨by fun_prop, scalarEntries_map_curry⟩
  exact (measurePreserving_arrowProdEquivProdArrow (RealRow h) (RealRow h) (Fin n)
    (fun _ => gaussianProductLaw (Fin h)) (fun _ => gaussianProductLaw (Fin h))).symm.comp
      (hc.prod hc)

theorem fourRealRows_preserving (n h : ℕ) :
    MeasurePreserving (fourRealRows n h) (fourGaussianLaw n h)
      (Measure.pi (fun _ : Fin n => fourRealRowLaw h)) := by
  exact (measurePreserving_arrowProdEquivProdArrow (PairRealRow h) (PairRealRow h) (Fin n)
    (fun _ => pairRealRowLaw h) (fun _ => pairRealRowLaw h)).symm.comp
      ((pairRealRows_preserving n h).prod (pairRealRows_preserving n h))

def normalizedRow (h : ℕ) (s : Bool) (x : PairRealRow h) : EuclideanSpace ℂ (Fin h) :=
  (MeasurableEquiv.toLp 2 (Fin h → ℂ))
    (fun j => normalizedCoordinate h s (x.1 j) (x.2 j))

def normalizedProductRow (h : ℕ) (s t : Bool) (x : FourRealRow h) :
    EuclideanSpace ℂ (Fin h × Fin h) :=
  (MeasurableEquiv.toLp 2 ((Fin h × Fin h) → ℂ))
    (fun p => normalizedRow h s x.1 p.1 * normalizedRow h t x.2 p.2)

/-- The actual normalized complex Gaussian product-state distribution. -/
def complexProductStateLaw (h : ℕ) (s t : Bool) :
    Measure (EuclideanSpace ℂ (Fin h × Fin h)) :=
  (fourRealRowLaw h).map (normalizedProductRow h s t)

def actualProductStates (n h : ℕ) (s t : Bool) (x : FourEntries n h) (i : Fin n) :
    EuclideanSpace ℂ (Fin h × Fin h) :=
  normalizedProductRow h s t (fourRealRows n h x i)

theorem measurable_normalizedProductRow (h : ℕ) (s t : Bool) :
    Measurable (normalizedProductRow h s t) := by
  unfold normalizedProductRow normalizedRow normalizedCoordinate
  fun_prop

instance complexProductStateLaw_probability (h : ℕ) (s t : Bool) :
    IsProbabilityMeasure (complexProductStateLaw h s t) :=
  Measure.isProbabilityMeasure_map (measurable_normalizedProductRow h s t).aemeasurable

/-- Exact joint law: for each fixed sign pair, the product states are iid. -/
theorem actualProductStates_joint_law (n h : ℕ) (s t : Bool) :
    (fourGaussianLaw n h).map (actualProductStates n h s t) =
      Measure.pi (fun _ : Fin n => complexProductStateLaw h s t) := by
  have hp := measurePreserving_pi
    (fun _ : Fin n => fourRealRowLaw h)
    (fun _ : Fin n => complexProductStateLaw h s t)
    (f := fun _ => normalizedProductRow h s t)
    (fun _ => ⟨measurable_normalizedProductRow h s t, rfl⟩)
  exact (hp.comp (fourRealRows_preserving n h)).map_eq

/-- Every individual product state has the same actual complex Gaussian law. -/
theorem actualProductStates_marginal (n h : ℕ) (s t : Bool) (i : Fin n) :
    (fourGaussianLaw n h).map (fun x => actualProductStates n h s t x i) =
      complexProductStateLaw h s t := by
  have hp : MeasurePreserving (actualProductStates n h s t) (fourGaussianLaw n h)
      (Measure.pi (fun _ : Fin n => complexProductStateLaw h s t)) :=
    ⟨by
      unfold actualProductStates fourRealRows pairRealRows
      exact measurable_pi_iff.mpr (fun i => (measurable_normalizedProductRow h s t).comp (by fun_prop)),
      actualProductStates_joint_law n h s t⟩
  exact ((measurePreserving_eval (fun _ : Fin n => complexProductStateLaw h s t) i).comp hp).map_eq

/-- Independence is a conclusion, not a premise in the source-facing model. -/
theorem actualProductStates_independent (n h : ℕ) (s t : Bool) :
    iIndepFun (fun i : Fin n => fun x => actualProductStates n h s t x i)
      (fourGaussianLaw n h) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ?_)).mpr
  · rw [actualProductStates_joint_law]
    congr 1
    funext i
    exact (actualProductStates_marginal n h s t i).symm
  · unfold actualProductStates fourRealRows pairRealRows
    exact ((measurable_normalizedProductRow h s t).comp (by fun_prop)).aemeasurable

#print axioms fourRealRows_preserving
#print axioms actualProductStates_joint_law
#print axioms actualProductStates_independent
end AHHGaussian
