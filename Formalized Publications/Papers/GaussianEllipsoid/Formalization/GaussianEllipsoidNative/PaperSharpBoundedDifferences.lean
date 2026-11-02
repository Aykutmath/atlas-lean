import UCProductConcentration
import UCFreeEnergyConcentration

noncomputable section
open MeasureTheory ProbabilityTheory
open GaussianEllipsoid.UCProductConcentration
open scoped BigOperators NNReal ENNReal
namespace GaussianEllipsoid.PaperSharpBoundedDifferences
variable {X : Type*} [MeasurableSpace X] [Nonempty X]

theorem product_centered_mgf (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M c : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : 0 ≤ c) (hbd : boundedDifferences f c)
    (t : ℝ) :
    (∫ x, Real.exp (t*(f x-∫ y, f y ∂productLaw μ n)) ∂productLaw μ n) ≤
      Real.exp ((n:ℝ)*c^2*t^2/8) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i : Fin 0 => Fin.elim0 i) := by
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp
  | succ n ih =>
    let F : X × (Fin n → X) → ℝ := fun z => f (Fin.cons z.1 z.2)
    have hmF : Measurable F := hf.comp (measurable_cons n)
    have hiF : Integrable F (μ.prod (productLaw μ n)) :=
      integrable_of_abs_bound hmF (fun z => hM _)
    let g : (Fin n → X) → ℝ := fun u => ∫ x, f (Fin.cons x u) ∂μ
    have hmg : Measurable g := hmF.stronglyMeasurable.integral_prod_left'.measurable
    have hgM : ∀ u, |g u| ≤ M := fun u => integral_abs_le_const fun x => hM _
    have hig : Integrable g (productLaw μ n) := integrable_of_abs_bound hmg hgM
    have hmf (u : Fin n → X) : Measurable (fun x => f (Fin.cons x u)) :=
      hmF.comp (measurable_id.prodMk measurable_const)
    have hif (u : Fin n → X) : Integrable (fun x => f (Fin.cons x u)) μ :=
      integrable_of_abs_bound (hmf u) (fun x => hM _)
    have hgbd : boundedDifferences g c := by
      intro u i y
      change |(∫ x, f (Fin.cons x (Function.update u i y)) ∂μ)-
        ∫ x, f (Fin.cons x u) ∂μ| ≤ c
      rw [← integral_sub (hif _) (hif _)]
      apply integral_abs_le_const
      intro x
      have he : Fin.cons x (Function.update u i y) = Function.update (Fin.cons x u : Fin (n+1) → X) i.succ y := by
        simpa only [Fin.insertNth_zero', Fin.succAbove_zero] using
          (Fin.insertNth_update (α := fun _ : Fin (n+1) => X) (0 : Fin (n+1)) x i y u)
      rw [he]
      exact hbd _ _ _
    have hmean : (∫ x, f x ∂productLaw μ (n+1)) = ∫ u, g u ∂productLaw μ n := by
      simpa only [Fin.insertNth_zero', g] using
        BMFiniteProductReplacement.integral_pi_insertNth μ (0 : Fin (n+1)) f
          (integrable_of_abs_bound hf hM)
    have hslice (u : Fin n → X) :
        (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ) ≤ Real.exp (c^2*t^2/8) := by
      let S : Set ℝ := Set.range (fun x => f (Fin.cons x u))
      have hS : S.Nonempty := Set.range_nonempty _
      have hbS : BddBelow S := ⟨-M, by
        rintro z ⟨x,rfl⟩
        exact (abs_le.mp (hM _)).1⟩
      have hmem : ∀ x, f (Fin.cons x u) ∈ Set.Icc (sInf S) (sInf S+c) := by
        intro x
        refine ⟨csInf_le hbS ⟨x,rfl⟩, ?_⟩
        have hl : f (Fin.cons x u)-c ≤ sInf S := by
          apply le_csInf hS
          rintro z ⟨y,rfl⟩
          have hh := hbd (Fin.cons y u) (0 : Fin (n+1)) x
          simp only [← Fin.insertNth_zero', Fin.update_insertNth] at hh
          simp only [Fin.insertNth_zero'] at hh
          linarith [(abs_le.mp hh).2]
        linarith
      have hh := (hasSubgaussianMGF_of_mem_Icc (hmf u).aemeasurable
        (ae_of_all μ hmem)).mgf_le t
      change (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ) ≤ _ at hh
      convert hh using 1 <;>
        simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat,
          Real.norm_eq_abs, show sInf S+c-sInf S=c by ring, abs_of_nonneg hc] <;> ring
    have hiExp := centered_exp_integrable (μ := productLaw μ (n+1)) hf hM t
    have hExp : (∫ x, Real.exp (t*(f x-∫ y, f y ∂productLaw μ (n+1)))
        ∂productLaw μ (n+1)) =
      ∫ u, ∫ x, Real.exp (t*(f (Fin.cons x u)-∫ y, g y ∂productLaw μ n)) ∂μ
        ∂productLaw μ n := by
      rw [BMFiniteProductReplacement.integral_pi_insertNth μ (0 : Fin (n+1)) _ hiExp]
      simp only [Fin.insertNth_zero', hmean]
    have hfactor (u : Fin n → X) :
        (∫ x, Real.exp (t*(f (Fin.cons x u)-∫ y, g y ∂productLaw μ n)) ∂μ) =
      (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ)*
        Real.exp (t*(g u-∫ y, g y ∂productLaw μ n)) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all μ fun x => by dsimp only; rw [← Real.exp_add]; congr 1; ring
    rw [hExp]
    simp_rw [hfactor]
    have hiProd : Integrable (fun u =>
        (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ)*
          Real.exp (t*(g u-∫ y, g y ∂productLaw μ n))) (productLaw μ n) := by
      have hi' : Integrable (fun z : X × (Fin n → X) =>
          Real.exp (t*(f (Fin.cons z.1 z.2)-∫ y, g y ∂productLaw μ n)))
          (μ.prod (productLaw μ n)) := by
        apply integrable_exp_mul_of_mem_Icc ((hmF.sub_const _).aemeasurable)
        apply ae_of_all
        intro z
        show F z - (∫ y, g y ∂productLaw μ n) ∈
          Set.Icc (-M-(∫ y, g y ∂productLaw μ n)) (M-(∫ y, g y ∂productLaw μ n))
        exact ⟨sub_le_sub_right (abs_le.mp (hM _)).1 _,
          sub_le_sub_right (abs_le.mp (hM _)).2 _⟩
      have hr := hi'.integral_prod_right
      simpa only [hfactor] using hr
    calc
      _ ≤ ∫ u, Real.exp (c^2*t^2/8)*Real.exp (t*(g u-∫ y, g y ∂productLaw μ n))
          ∂productLaw μ n :=
        integral_mono hiProd ((centered_exp_integrable hmg hgM t).const_mul _)
          (fun u => mul_le_mul_of_nonneg_right (hslice u) (Real.exp_nonneg _))
      _ = Real.exp (c^2*t^2/8)*
          (∫ u, Real.exp (t*(g u-∫ y, g y ∂productLaw μ n)) ∂productLaw μ n) := by
        rw [integral_const_mul]
      _ ≤ Real.exp (c^2*t^2/8)*Real.exp ((n:ℝ)*c^2*t^2/8) :=
        mul_le_mul_of_nonneg_left (ih g hmg hgM hgbd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring


theorem product_hasSubgaussianMGF (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M c : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : 0 ≤ c) (hbd : boundedDifferences f c) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂productLaw μ n)
      ⟨(n:ℝ)*c^2/4, by positivity⟩ (productLaw μ n) where
  integrable_exp_mul := centered_exp_integrable hf hM
  mgf_le t := by
    change (∫ x, Real.exp (t*(f x-∫ y,f y ∂productLaw μ n)) ∂productLaw μ n) ≤
      Real.exp (((n:ℝ)*c^2/4)*t^2/2)
    convert product_centered_mgf μ n f hf M c hM hc hbd t using 1 <;> ring

theorem normalized_product_two_sided (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0<n) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, |f x|≤M) (hbd : boundedDifferences f (1/(n:ℝ)))
    (t : ℝ) (ht : 0≤t) :
    (productLaw μ n).real {x | t < |f x-∫ y,f y ∂productLaw μ n|} ≤
      2*Real.exp (-2*(n:ℝ)*t^2) := by
  have hs := product_hasSubgaussianMGF μ n f hf M (1/(n:ℝ)) hM (by positivity) hbd
  have hp := hs.measure_ge_le ht
  have hm := hs.neg.measure_ge_le ht
  have hsub : {x | t < |f x-∫ y,f y ∂productLaw μ n|} ⊆
      {x | t≤f x-∫ y,f y ∂productLaw μ n} ∪
      {x | t≤-(f x-∫ y,f y ∂productLaw μ n)} := by
    intro x hx
    change t < |f x-∫ y,f y ∂productLaw μ n| at hx
    rcases lt_abs.mp hx with h|h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have h := (measureReal_mono (μ := productLaw μ n) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hp hm))
  apply h.trans_eq
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : -t^2/(2*((n:ℝ)*(1/(n:ℝ))^2/4)) = -2*(n:ℝ)*t^2 := by
    field_simp
    <;> ring
  change Real.exp (-t^2/(2*((n:ℝ)*(1/(n:ℝ))^2/4))) +
    Real.exp (-t^2/(2*((n:ℝ)*(1/(n:ℝ))^2/4))) = _
  rw [he]
  ring

open BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition
variable {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]

theorem paper_freeEnergy_concentration (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (hweight : ∀ a,D.weight a=(Fintype.card κ:ℝ)⁻¹)
    (hβ : 0<D.beta) {n : ℕ} (hn : 0<n)
    (hloss : ∀ t,0≤D.potential t ∧ D.potential t≤1)
    (q : X→κ→ℝ) (hq : Measurable q) (c : Fin n→κ→ℝ)
    (t : ℝ) (ht : 0≤t) :
    (productLaw μ n).real {x |
      t < |UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i)-
        ∫ y, UCActualFreeEnergy.freeEnergy D (fun i => q (y i)+c i) ∂productLaw μ n|} ≤
      2*Real.exp (-2*(n:ℝ)*t^2) := by
  apply normalized_product_two_sided μ n hn _
    (UCFreeEnergyConcentration.measurable_freeEnergy D q hq c) 1 _ _ t ht
  · intro x
    have h := UCFreeEnergyBridge.freeEnergy_mem_unit_interval D hweight hβ hn hloss
      (fun i => q (x i)+c i)
    rw [abs_of_nonneg h.1]
    exact h.2
  · intro x i z
    exact UCFreeEnergyBridge.freeEnergy_row_difference D hweight hβ hn hloss q c x i z

theorem paper_freeEnergy_margin (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (hweight : ∀ a,D.weight a=(Fintype.card κ:ℝ)⁻¹)
    (hβ : 0<D.beta) {n : ℕ} (hn : 0<n)
    (hloss : ∀ t,0≤D.potential t ∧ D.potential t≤1)
    (q : X→κ→ℝ) (hq : Measurable q) (c : Fin n→κ→ℝ)
    (θ : ℝ) (hθ : 0≤θ)
    (hmean : 7*θ/8 ≤ ∫ y, UCActualFreeEnergy.freeEnergy D
      (fun i => q (y i)+c i) ∂productLaw μ n) :
    (productLaw μ n).real {x | UCActualFreeEnergy.freeEnergy D
      (fun i => q (x i)+c i) < 3*θ/4} ≤
      2*Real.exp (-(n:ℝ)*θ^2/32) := by
  have hh := paper_freeEnergy_concentration μ D hweight hβ hn hloss q hq c
    (θ/8) (by positivity)
  apply (measureReal_mono (μ := productLaw μ n) (show {x | UCActualFreeEnergy.freeEnergy D
      (fun i => q (x i)+c i) < 3*θ/4} ⊆ _ from ?_)).trans (hh.trans_eq ?_)
  · intro x hx
    change θ/8 < |UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i)-
      ∫ y, UCActualFreeEnergy.freeEnergy D (fun i => q (y i)+c i) ∂productLaw μ n|
    change UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i) < 3*θ/4 at hx
    apply lt_abs.mpr
    right
    linarith
  · congr 2
    ring

#print axioms paper_freeEnergy_margin
#print axioms paper_freeEnergy_concentration
#print axioms product_centered_mgf
#print axioms product_hasSubgaussianMGF
end GaussianEllipsoid.PaperSharpBoundedDifferences
