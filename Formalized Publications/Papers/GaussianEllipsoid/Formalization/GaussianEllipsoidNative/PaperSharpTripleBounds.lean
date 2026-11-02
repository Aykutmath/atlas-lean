import PaperThirdQuadraticBound

noncomputable section
open MeasureTheory GaussianTensorMoments BMQuadraticStein MvPolynomial
open scoped BigOperators
namespace GaussianEllipsoid.PaperSharpTripleBounds
open PaperThirdQuadraticBound
variable {d : ℕ}

def symmetricPart (A : Matrix (Fin d) (Fin d) ℝ) := (1/2:ℝ) • (A+A.transpose)

lemma symmetricPart_transpose (A : Matrix (Fin d) (Fin d) ℝ) :
    (symmetricPart A).transpose=symmetricPart A := by
  ext i j
  simp only [symmetricPart,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply]
  ring

lemma symmetricPart_trace (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace (symmetricPart A)=Matrix.trace A := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i hi
  simp [symmetricPart,Matrix.diag_apply]
  ring

lemma frobeniusSq_symmetricPart_le (A : Matrix (Fin d) (Fin d) ℝ) :
    frobeniusSq (symmetricPart A)≤frobeniusSq A := by
  unfold frobeniusSq
  calc
    _ ≤ ∑ i,∑ j,((A i j)^2+(A j i)^2)/2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [symmetricPart,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.transpose_apply]
      nlinarith [sq_nonneg (A i j-A j i)]
    _ = _ := by
      simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => (A j i)^2)]
      ring

theorem triple_trace_frobenius_sharp (A B C : Matrix (Fin d) (Fin d) ℝ)
    {τ : ℝ} (hτ : 0≤τ) (hτ1 : τ≤1)
    (hA : spectralNorm A≤τ) (hB : spectralNorm B≤τ)
    (hFA : frobeniusSq A≤1) (hFC : frobeniusSq C≤1) :
    (Matrix.trace (A*B*C))^2≤τ^2 ∧ frobeniusSq (A*B*C)≤τ^4 := by
  refine ⟨(triple_bounds A B C hτ hτ1 hA hB hFA hFC).1,?_⟩
  have ha := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hb := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hBC : frobeniusSq (B*C)≤τ^2 := calc
    _ ≤ spectralNorm B^2*frobeniusSq C := UCFrobeniusStein.frobeniusSq_mul_le_spectral_frobenius B C
    _ ≤ τ^2*1 := mul_le_mul hb hFC (frobeniusSq_nonneg _) (sq_nonneg _)
    _ = _ := mul_one _
  rw [Matrix.mul_assoc]
  calc
    _ ≤ spectralNorm A^2*frobeniusSq (B*C) := UCFrobeniusStein.frobeniusSq_mul_le_spectral_frobenius A (B*C)
    _ ≤ τ^2*τ^2 := mul_le_mul ha hBC (frobeniusSq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

lemma polynomial_abs_integral_sq_le (P : MvPolynomial (Fin d) ℝ) :
    (∫ w,|eval w P| ∂gaussianProductLaw (Fin d))^2≤expectation (P^2) := by
  let μ := gaussianProductLaw (Fin d)
  let a := ∫ w,|eval w P| ∂μ
  have hi := (gaussianProductLaw_integrable_polynomial P).norm
  have hi' : Integrable (fun w => |eval w P|) μ := by simpa only [Real.norm_eq_abs] using hi
  have hsq : Integrable (fun w => (eval w P)^2) μ := by
    have h := gaussianProductLaw_integrable_polynomial (P^2)
    convert h using 1
    funext w
    exact (map_pow (eval w) P 2).symm
  have hn : 0≤∫ w,(|eval w P|-a)^2 ∂μ := integral_nonneg fun w => sq_nonneg _
  have he (w : Fin d→ℝ) : (|eval w P|-a)^2 = (eval w P)^2-2*a*|eval w P|+a^2 := by
    nlinarith [sq_abs (eval w P)]
  simp_rw [he] at hn
  have hi1 : Integrable (fun w => (eval w P)^2-2*a*|eval w P|) μ :=
    hsq.sub (hi'.const_mul (2*a))
  rw [integral_add hi1 (integrable_const _),
    integral_sub hsq (hi'.const_mul (2*a)),integral_const_mul] at hn
  simp only [integral_const,probReal_univ,one_smul] at hn
  have heq : (∫ w,(eval w P)^2 ∂μ)=expectation (P^2) := by
    change (∫ w,(eval w P)^2 ∂μ) = ∫ w,eval w (P^2) ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => (map_pow (eval w) P 2).symm
  rw [heq] at hn
  change a^2≤_
  nlinarith

/-- The source's sharper tau+sqrt(2)tau² intermediate estimate, before
relaxing to an unspecified universal multiple of tau. -/
theorem quadratic_abs_integral_sharp (A : Matrix (Fin d) (Fin d) ℝ) {τ : ℝ}
    (hτ : 0≤τ) (ht : (Matrix.trace A)^2≤τ^2) (hf : frobeniusSq A≤τ^4) :
    (∫ w,|∑ i,∑ j,A i j*(w i*w j)| ∂gaussianProductLaw (Fin d))≤τ+Real.sqrt 2*τ^2 := by
  have hm := polynomial_abs_integral_sq_le (quadratic A)
  rw [quadratic_second_moment] at hm
  have hv := expectation_centeredQuadratic_sq_le A
  change expectation ((centeredQuadratic A)^2)≤2*frobeniusSq A at hv
  simp_rw [eval_quadratic] at hm
  apply (sq_le_sq₀ (integral_nonneg fun w => abs_nonneg _) (by positivity)).mp
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0≤Real.sqrt 2*τ^3 := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hτ _)
  nlinarith

theorem paper_symmetric_triple_bound (A B C : Matrix (Fin d) (Fin d) ℝ)
    {τ : ℝ} (hτ : 0≤τ) (hτ1 : τ≤1)
    (hA : spectralNorm A≤τ) (hB : spectralNorm B≤τ)
    (hFA : frobeniusSq A≤1) (hFC : frobeniusSq C≤1) :
    let Q := symmetricPart (A*B*C)
    |Matrix.trace Q|≤τ ∧ Real.sqrt (frobeniusSq Q)≤τ^2 ∧
      (∫ w,|∑ i,∑ j,Q i j*(w i*w j)| ∂gaussianProductLaw (Fin d))≤τ+Real.sqrt 2*τ^2 := by
  have ht := triple_trace_frobenius_sharp A B C hτ hτ1 hA hB hFA hFC
  have hf := (frobeniusSq_symmetricPart_le (A*B*C)).trans ht.2
  have htrace : (Matrix.trace (symmetricPart (A*B*C)))^2≤τ^2 := by
    rw [symmetricPart_trace]
    exact ht.1
  dsimp only
  refine ⟨?_,?_,quadratic_abs_integral_sharp _ hτ htrace hf⟩
  · exact (sq_le_sq₀ (abs_nonneg _) hτ).mp (by simpa only [sq_abs] using htrace)
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨sq_nonneg _,by nlinarith⟩

theorem paper_symmetric_quadratic_variance (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.transpose=Q) :
    (∫ w,((∑ i,∑ j,Q i j*(w i*w j))-Matrix.trace Q)^2
      ∂gaussianProductLaw (Fin d))=2*frobeniusSq Q := by
  calc
    _ = expectation ((centeredQuadratic Q)^2) := by
      change (∫ w,((∑ i,∑ j,Q i j*(w i*w j))-Matrix.trace Q)^2
        ∂gaussianProductLaw (Fin d)) = ∫ w,eval w ((centeredQuadratic Q)^2)
        ∂gaussianProductLaw (Fin d)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by simp only [map_pow,eval_centeredQuadratic]
    _ = _ := by
      simpa only [pow_two,frobeniusSq] using
        expectation_centeredQuadratic_covariance_symmetric Q Q hQ

theorem paper_symmetric_triple_abs_le_universal (A B C : Matrix (Fin d) (Fin d) ℝ)
    {τ : ℝ} (hτ : 0≤τ) (hτ1 : τ≤1)
    (hA : spectralNorm A≤τ) (hB : spectralNorm B≤τ)
    (hFA : frobeniusSq A≤1) (hFC : frobeniusSq C≤1) :
    (∫ w,|∑ i,∑ j,symmetricPart (A*B*C) i j*(w i*w j)|
      ∂gaussianProductLaw (Fin d))≤(1+Real.sqrt 2)*τ := by
  have h := (paper_symmetric_triple_bound A B C hτ hτ1 hA hB hFA hFC).2.2
  apply h.trans
  have ht : τ^2≤τ := by nlinarith
  have hs := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg 2)
  nlinarith

#print axioms paper_symmetric_quadratic_variance
#print axioms paper_symmetric_triple_abs_le_universal
#print axioms triple_trace_frobenius_sharp
#print axioms quadratic_abs_integral_sharp
#print axioms paper_symmetric_triple_bound
end GaussianEllipsoid.PaperSharpTripleBounds
