import AHHGaussianRowLaw
import AHHAlgebraBridges

/-! Literal manuscript bridges: actual independent Gaussian states equal the
four-sign algebraic states, including all normalization factors. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators
namespace AHHGaussian

/-- Boolean signs enumerate exactly the real signs {-1,1}. -/
theorem sign_eq_neg_one_or_one (s : Bool) : sign s = -1 ∨ sign s = 1 := by
  cases s <;> simp [sign]

theorem exists_bool_sign (s : ℝ) (hs : s = -1 ∨ s = 1) : ∃ b : Bool, sign b = s := by
  rcases hs with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem normalizedProductRow_eq_productState (h : ℕ) (s t : Bool)
    (x : FourRealRow h) (p : Fin h × Fin h) :
    normalizedProductRow h s t x p =
      AHHAlgebraBridges.productState (h : ℝ) x.1.1 x.1.2 x.2.1 x.2.2 s t p := by
  change (_ / (Real.sqrt (2 * (h : ℝ)) : ℂ)) *
    (_ / (Real.sqrt (2 * (h : ℝ)) : ℂ)) = _
  rw [div_mul_div_comm]
  have hsqrt : (Real.sqrt (2 * (h : ℝ)) : ℂ) *
      (Real.sqrt (2 * (h : ℝ)) : ℂ) = 2 * (h : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg (2*h))
  rw [hsqrt]
  rfl

/-- The literal z_i=(a_i+i s a'_i)⊗(b_i+i t b'_i)/(2h). -/
theorem actualProductStates_eq_productState (n h : ℕ) (s t : Bool)
    (x : FourEntries n h) (i : Fin n) (p : Fin h × Fin h) :
    actualProductStates n h s t x i p =
      AHHAlgebraBridges.productState (h : ℝ)
        (fun j => x.1.1 (i,j)) (fun j => x.1.2 (i,j))
        (fun j => x.2.1 (i,j)) (fun j => x.2.2 (i,j)) s t p :=
  normalizedProductRow_eq_productState h s t (fourRealRows n h x i) p

/-- Exact iid law for the literal source formula (as coordinate vectors). -/
theorem literal_productStates_joint_law (n h : ℕ) (s t : Bool) :
    (fourGaussianLaw n h).map (fun x : FourEntries n h => fun i : Fin n =>
      (MeasurableEquiv.toLp 2 ((Fin h × Fin h) → ℂ))
        (AHHAlgebraBridges.productState (h : ℝ)
          (fun j => x.1.1 (i,j)) (fun j => x.1.2 (i,j))
          (fun j => x.2.1 (i,j)) (fun j => x.2.2 (i,j)) s t)) =
        Measure.pi (fun _ : Fin n => complexProductStateLaw h s t) := by
  convert actualProductStates_joint_law n h s t using 1
  congr 1
  funext x i
  ext p
  exact (actualProductStates_eq_productState n h s t x i p).symm

/-- The original norm² normalization remains exact inside the complete four-real
sample space, for the first complex factor. -/
theorem fourGaussianLaw_first_factor_expected_norm_sq (n h : ℕ) (hh : 0 < h)
    (s : Bool) (i : Fin n) :
    (∫ x : FourEntries n h, ‖normalizedFactor n h s x.1 i‖^2 ∂fourGaussianLaw n h) = 1 := by
  have he := integral_map (μ := fourGaussianLaw n h) (φ := Prod.fst)
    (f := fun x : PairEntries n h => ‖normalizedFactor n h s x i‖^2)
    measurable_fst.aemeasurable
    (by simp_rw [normalizedFactor_norm_sq]; fun_prop)
  have hm : (fourGaussianLaw n h).map Prod.fst = pairGaussianLaw n h := by
    simp [fourGaussianLaw]
  rw [hm] at he
  exact he.symm.trans (normalizedFactor_expected_norm_sq n h hh s i)

theorem fourGaussianLaw_second_factor_expected_norm_sq (n h : ℕ) (hh : 0 < h)
    (t : Bool) (i : Fin n) :
    (∫ x : FourEntries n h, ‖normalizedFactor n h t x.2 i‖^2 ∂fourGaussianLaw n h) = 1 := by
  have he := integral_map (μ := fourGaussianLaw n h) (φ := Prod.snd)
    (f := fun x : PairEntries n h => ‖normalizedFactor n h t x i‖^2)
    measurable_snd.aemeasurable
    (by simp_rw [normalizedFactor_norm_sq]; fun_prop)
  have hm : (fourGaussianLaw n h).map Prod.snd = pairGaussianLaw n h := by
    simp [fourGaussianLaw]
  rw [hm] at he
  exact he.symm.trans (normalizedFactor_expected_norm_sq n h hh t i)

#print axioms actualProductStates_eq_productState
#print axioms literal_productStates_joint_law
#print axioms fourGaussianLaw_first_factor_expected_norm_sq
#print axioms fourGaussianLaw_second_factor_expected_norm_sq
end AHHGaussian
