/-
Discharge of the Section 12 quotient bridge (paper Section 12): the
mixed-norm lower bound implies the quotient-residual upper bound, via
finite-dimensional quotient duality (instantiated on the range of the
centered measurement operator), the adjoint identity, and
operator/nuclear duality.
Mathematical source: paper.tex, Section 12.
-/
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.QuotientDuality

noncomputable section

open scoped Matrix

namespace GaussianEllipsoid

/-! ### Quadratic transpose invariance -/

/-- The quadratic form is invariant under transposition. -/
theorem quadratic_transpose {d : Nat} (H : Square d) (v : Vector d) :
    quadratic Hᵀ v = quadratic H v := by
  unfold quadratic
  rw [Matrix.mulVec_transpose, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

/-! ### The measurement operator as a linear map -/

/-- Scalar action on dot products, left. -/
theorem dot_smul_left {n : Nat} (c : ℝ) (u v : Vector n) :
    dotProduct (c • u) v = c * dotProduct u v := by
  simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]

/-- Scalar action on dot products, right. -/
theorem dot_smul_right {n : Nat} (c : ℝ) (u v : Vector n) :
    dotProduct u (c • v) = c * dotProduct u v := by
  simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm,
    ← Finset.mul_sum]

/-- The centered measurement operator, as a real linear map. -/
def measurementTLinear {d n : Nat} (x : Sample d n) :
    Square d →ₗ[ℝ] Vector n where
  toFun := measurementT x
  map_add' := by
    intro H₁ H₂
    have hA : measurementA x (H₁ + H₂)
        = measurementA x H₁ + measurementA x H₂ := by
      funext j
      simp only [measurementA, Pi.add_apply, quadratic,
        Matrix.add_mulVec, dotProduct_add]
    funext i
    simp only [measurementT, Pi.add_apply, hA, center_add, Pi.add_apply,
      add_div]
  map_smul' := by
    intro c H
    have hA : measurementA x (c • H) = c • measurementA x H := by
      funext j
      simp only [measurementA, Pi.smul_apply, quadratic,
        Matrix.smul_mulVec]
      rw [dot_smul_right]
      simp only [smul_eq_mul]
    funext i
    simp only [measurementT, Pi.smul_apply, hA, center_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]

/-! ### Quadratic expansion and a Fubini helper -/

/-- The quadratic form as an explicit double sum. -/
theorem quadratic_sum_form {d : Nat} (H : Square d) (v : Vector d) :
    quadratic H v = ∑ p, ∑ q, H p q * (v p * v q) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Reindexing a triple sum: move the last index first. `Finset.sum_comm`
cannot cross different index types, so this goes through product types. -/
theorem triple_sum_fubini {d n : Nat} (F : Fin d → Fin d → Fin n → ℝ) :
    (∑ p, ∑ q, ∑ i, F p q i) = ∑ i, ∑ p, ∑ q, F p q i := by
  let e : ((Fin d × Fin d) × Fin n) ≃ ((Fin n × Fin d) × Fin d) :=
    { toFun := fun z => ((z.2, z.1.1), z.1.2)
      invFun := fun y => ((y.1.2, y.2), y.1.1)
      left_inv := by intro z; obtain ⟨⟨a, b⟩, c⟩ := z; rfl
      right_inv := by intro y; obtain ⟨⟨c, a⟩, b⟩ := y; rfl }
  have hL : (∑ p, ∑ q, ∑ i, F p q i)
      = ∑ z : (Fin d × Fin d) × Fin n, F z.1.1 z.1.2 z.2 := by
    rw [← Fintype.sum_prod_type (fun w : Fin d × Fin d => ∑ i, F w.1 w.2 i)]
    rw [← Fintype.sum_prod_type
      (fun z : (Fin d × Fin d) × Fin n => F z.1.1 z.1.2 z.2)]
  have hR : (∑ i, ∑ p, ∑ q, F p q i)
      = ∑ y : (Fin n × Fin d) × Fin d, F y.1.2 y.2 y.1.1 := by
    rw [← Fintype.sum_prod_type (fun w : Fin n × Fin d => ∑ q, F w.2 q w.1)]
    rw [← Fintype.sum_prod_type
      (fun y : (Fin n × Fin d) × Fin d => F y.1.2 y.2 y.1.1)]
  rw [hL, hR]
  apply Fintype.sum_equiv e
  intro z
  rfl

/-- The dual mixed norm is nonnegative. -/
theorem dualMixed_nonneg {η : ℝ} {d n : Nat} (e : Vector n) :
    0 ≤ dualMixed η d n e := by
  unfold dualMixed
  calc (0 : ℝ) ≤ euclidNorm e / (d : ℝ) :=
        div_nonneg (euclidNorm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ max (‖e‖ / (η * Real.sqrt (d : ℝ))) (euclidNorm e / (d : ℝ)) :=
        le_max_right _ _

/-! ### Adjoint identity -/

/-- Pairing the centered measurements with a centered weight vector equals
the trace pairing with the centered adjoint. -/
theorem adjoint_identity {d n : Nat} (x : Sample d n) (H : Square d)
    (y : Vector n) (hy : ∑ i, y i = 0) :
    dotProduct (measurementT x H) y
      = ∑ p, ∑ q, H p q * (centeredAdjoint x y) p q := by
  have hcy : center y = y := center_eq_self_of_sum_zero y hy
  have hLHS : dotProduct (measurementT x H) y
      = (1 / Real.sqrt (d : ℝ)) * ∑ i, quadratic H (x i) * y i := by
    have e1 : measurementT x H
        = (1 / Real.sqrt (d : ℝ)) • center (measurementA x H) := by
      funext i
      simp only [measurementT, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [e1, dot_smul_left, center_selfAdjoint, hcy]
    simp only [dotProduct, measurementA]
  have hRHS : (∑ p, ∑ q, H p q * (centeredAdjoint x y) p q)
      = (1 / Real.sqrt (d : ℝ)) * ∑ i, y i * quadratic H (x i) := by
    have smul_entry : ∀ (c : ℝ) (M : Square d) (p q : Fin d),
        (c • M) p q = c * M p q := by
      intro c M p q
      have h : (c • M) p q = c • M p q := rfl
      rw [h, smul_eq_mul]
    have add_entry : ∀ (A B : Square d) (p q : Fin d),
        (A + B) p q = A p q + B p q := fun _ _ _ _ => rfl
    have zero_entry : ∀ (p q : Fin d), (0 : Square d) p q = 0 :=
      fun _ _ => rfl
    have sum_entry : ∀ (F : Fin n → Square d) (p q : Fin d),
        (∑ i, F i) p q = ∑ i, F i p q := by
      have gen : ∀ (s : Finset (Fin n)) (F : Fin n → Square d)
          (p q : Fin d), (∑ i ∈ s, F i) p q = ∑ i ∈ s, F i p q := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · intro F p q
          rw [Finset.sum_empty, Finset.sum_empty]
          exact zero_entry p q
        · intro a s has ih F p q
          rw [Finset.sum_insert has, Finset.sum_insert has, add_entry,
            ih F p q]
      intro F p q
      exact gen Finset.univ F p q
    have e2 : ∀ p q, (centeredAdjoint x y) p q
        = (1 / Real.sqrt (d : ℝ)) * ∑ i, y i * ((x i) p * (x i) q) := by
      intro p q
      simp only [centeredAdjoint, smul_entry, sum_entry,
        Matrix.vecMulVec_apply]
    have h2a : (∑ p, ∑ q, H p q * (centeredAdjoint x y) p q)
        = ∑ i, ∑ p, ∑ q, (1 / Real.sqrt (d : ℝ))
          * (H p q * (y i * ((x i) p * (x i) q))) := by
      simp only [e2]
      have t1 : (∑ p, ∑ q, H p q * ((1 / Real.sqrt (d : ℝ))
            * ∑ i, y i * ((x i) p * (x i) q)))
          = ∑ p, ∑ q, (1 / Real.sqrt (d : ℝ))
            * (H p q * ∑ i, y i * ((x i) p * (x i) q)) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        ring
      rw [t1]
      simp only [Finset.mul_sum]
      exact triple_sum_fubini
        (fun p q i => (1 / Real.sqrt (d : ℝ))
          * (H p q * (y i * ((x i) p * (x i) q))))
    have h2b : (1 / Real.sqrt (d : ℝ)) * ∑ i, y i * quadratic H (x i)
        = ∑ i, ∑ p, ∑ q, (1 / Real.sqrt (d : ℝ))
          * (H p q * (y i * ((x i) p * (x i) q))) := by
      simp only [quadratic_sum_form, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [h2a]
    exact h2b.symm
  rw [hLHS, hRHS]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

section OpScope

open scoped Matrix.Norms.L2Operator

/-! ### Transpose invariance and symmetrization -/

/-- Operator norm is invariant under transposition (C* argument:
`‖star H‖ = ‖H‖` and `star H = Hᵀ` over `ℝ`). -/
theorem matrixOpNorm_transpose {d : Nat} (H : Square d) :
    matrixOpNorm Hᵀ = matrixOpNorm H := by
  unfold matrixOpNorm
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.star_eq_conjTranspose]
  exact norm_star H

/-- Symmetrization of a fiber element stays in the fiber over the same
right-hand side without increasing the operator norm. -/
theorem exists_symmetric_fiber_le {d n : Nat} (x : Sample d n) (H : Square d)
    (e : Vector n) (hH : measurementT x H = e) :
    ∃ H' : Square d, H'.IsSymm ∧ measurementT x H' = e
      ∧ matrixOpNorm H' ≤ matrixOpNorm H := by
  refine ⟨(1 / 2 : ℝ) • (H + Hᵀ), ?_, ?_, ?_⟩
  · unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_transpose, smul_add, add_comm ((1 / 2 : ℝ) • Hᵀ),
      ← smul_add]
  · have hTt : measurementT x Hᵀ = measurementT x H := by
      funext i
      simp only [measurementT]
      congr 1
      have hA : measurementA x Hᵀ = measurementA x H := by
        funext j
        simp only [measurementA]
        exact quadratic_transpose H (x j)
      rw [hA]
    have h1 : measurementT x ((1 / 2 : ℝ) • (H + Hᵀ))
        = (1 / 2 : ℝ) • measurementT x (H + Hᵀ) :=
      (measurementTLinear x).map_smul _ _
    have h2 : measurementT x (H + Hᵀ)
        = measurementT x H + measurementT x Hᵀ :=
      (measurementTLinear x).map_add _ _
    rw [h1, h2, hTt, hH]
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  · have hsm : matrixOpNorm ((1 / 2 : ℝ) • (H + Hᵀ))
        = (1 / 2) * matrixOpNorm (H + Hᵀ) := by
      rw [matrixOpNorm_smul]
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hadd : matrixOpNorm (H + Hᵀ)
        ≤ matrixOpNorm H + matrixOpNorm Hᵀ :=
      matrixOpNorm_add_le H Hᵀ
    rw [matrixOpNorm_transpose] at hadd
    rw [hsm]
    linarith [hadd, matrixOpNorm_nonneg H]

/-- The symmetric fiber infimum is below the full fiber infimum. -/
theorem kappa_le_sInf_full {d n : Nat} (x : Sample d n) (S : Square d)
    (hne : {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r}.Nonempty) :
    kappa d n x S
      ≤ sInf {r : Real | ∃ H : Square d,
        measurementT x H = -center (residual x S)
          ∧ matrixOpNorm H = r} := by
  have hbdd : BddBelow {r : Real | ∃ H : Square d,
      measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨H, -, rfl⟩
    exact matrixOpNorm_nonneg H
  have hbddS : BddBelow {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨H, -, -, rfl⟩
    exact matrixOpNorm_nonneg H
  have hneF : {r : Real | ∃ H : Square d,
      measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r}.Nonempty := by
    obtain ⟨r, H, -, hHT, hHr⟩ := hne
    exact ⟨r, H, hHT, hHr⟩
  apply le_csInf hneF
  intro r hr
  obtain ⟨H, hHT, hHr⟩ := hr
  obtain ⟨H', hH's, hH'T, hH'le⟩ :=
    exists_symmetric_fiber_le x H _ hHT
  have hmem : matrixOpNorm H' ∈ {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} :=
    ⟨H', hH's, hH'T, rfl⟩
  have hle := csInf_le hbddS hmem
  unfold kappa at hle ⊢
  rw [← hHr]
  exact le_trans hle hH'le

end OpScope

/-! ### Operator-norm normed-space instances (helper H2, scoped) -/

namespace OpNormInst

/-- Operator-norm `Norm` instance on square matrices. -/
scoped instance opNormNorm {d : Nat} : Norm (Square d) where
  norm := matrixOpNorm

end OpNormInst

/-- Operator-norm triangle inequality for subtraction. -/
theorem matrixOpNorm_sub_le {d : Nat} (A B : Square d) :
    matrixOpNorm (A - B) ≤ matrixOpNorm A + matrixOpNorm B := by
  have h : A - B = A + (-B) := by abel
  rw [h]
  calc matrixOpNorm (A + (-B))
      ≤ matrixOpNorm A + matrixOpNorm (-B) := matrixOpNorm_add_le _ _
    _ = matrixOpNorm A + matrixOpNorm B := by rw [matrixOpNorm_neg]

namespace OpNormInst

/-- Operator-norm `NormedAddCommGroup` instance on square matrices. -/
scoped instance opNormNormedAddCommGroup {d : Nat} :
    NormedAddCommGroup (Square d) where
  toAddCommGroup := inferInstance
  norm := matrixOpNorm
  dist := fun X Y => matrixOpNorm (X - Y)
  dist_self := fun X => by
    show matrixOpNorm (X - X) = 0
    rw [sub_self, matrixOpNorm_zero]
  dist_comm := fun X Y => by
    show matrixOpNorm (X - Y) = matrixOpNorm (Y - X)
    have h : Y - X = -(X - Y) := by abel
    rw [h, matrixOpNorm_neg]
  dist_triangle := fun X Y Z => by
    show matrixOpNorm (X - Z)
      ≤ matrixOpNorm (X - Y) + matrixOpNorm (Y - Z)
    have h : X - Z = (X - Y) + (Y - Z) := by abel
    rw [h]
    exact matrixOpNorm_add_le _ _
  eq_of_dist_eq_zero := fun {X Y} h => by
    have h' : matrixOpNorm (X - Y) = 0 := h
    have hsub : X - Y = 0 := (matrixOpNorm_eq_zero_iff _).mp h'
    exact sub_eq_zero.mp hsub
  dist_eq := fun X Y => by
    show matrixOpNorm (X - Y) = matrixOpNorm (-X + Y)
    have h : -X + Y = -(X - Y) := by abel
    rw [h, matrixOpNorm_neg]

/-- Operator-norm `NormedSpace` instance on square matrices. -/
scoped instance opNormNormedSpace {d : Nat} : NormedSpace ℝ (Square d) where
  toModule := inferInstance
  norm_smul_le := fun c A => by
    show matrixOpNorm (c • A) ≤ ‖c‖ * matrixOpNorm A
    exact le_of_eq (matrixOpNorm_smul c A)

/-- Bridge: norm-derived `AddCommMonoid`, matching the instance paths
used inside quotient duality (avoids diamonds with direct matrix
instances). -/
scoped instance (priority := 10000) opAddCommMonoid {d : Nat} :
    AddCommMonoid (Square d) :=
  @AddCommGroup.toAddCommMonoid _
    (@NormedAddCommGroup.toAddCommGroup _ (@opNormNormedAddCommGroup d))

/-- Bridge: norm-derived `Module`. -/
scoped instance (priority := 10000) opModule {d : Nat} :
    Module ℝ (Square d) :=
  @NormedSpace.toModule _ _ _ _ (@opNormNormedSpace d)

/-- Bridge: norm-derived `TopologicalSpace`. -/
scoped instance (priority := 10000) opTopo {d : Nat} :
    TopologicalSpace (Square d) :=
  @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
    (@MetricSpace.toPseudoMetricSpace _
      (@NormedAddCommGroup.toMetricSpace _ (@opNormNormedAddCommGroup d))))

/-- Bridge: submodule `AddCommMonoid` via its normed structure. -/
scoped instance (priority := 10000) subAddCommMonoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Submodule ℝ E}
    [NormedAddCommGroup s] : AddCommMonoid s :=
  @AddCommGroup.toAddCommMonoid _
    (@NormedAddCommGroup.toAddCommGroup _ inferInstance)

/-- Bridge: submodule `Module` via its normed structure. -/
scoped instance (priority := 10000) subModule {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Submodule ℝ E}
    [NormedSpace ℝ s] : Module ℝ s :=
  @NormedSpace.toModule _ _ _ _ inferInstance

/-- Bridge: submodule `TopologicalSpace` via its normed structure. -/
scoped instance (priority := 10000) subTopo {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Submodule ℝ E}
    [NormedAddCommGroup s] : TopologicalSpace s :=
  @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
    (@MetricSpace.toPseudoMetricSpace _
      (@NormedAddCommGroup.toMetricSpace _ inferInstance)))

end OpNormInst

/-! ### Centering reductions and degenerate cases -/

/-- Measurements sum to zero: the range of `T_d` lies in the centered
subspace. -/
theorem measurementT_sum_zero {d n : Nat} (hn : 0 < n) (x : Sample d n)
    (H : Square d) : ∑ i, measurementT x H i = 0 := by
  have h : ∑ i, measurementT x H i
      = (∑ i, center (measurementA x H) i) * (Real.sqrt (d : ℝ))⁻¹ := by
    simp only [measurementT, div_eq_mul_inv]
    rw [Finset.sum_mul]
  rw [h, sum_center hn, zero_mul]

/-- Pairing against a centered vector factors through centering. -/
theorem dot_center_right {n : Nat} (w s : Vector n) (hs : ∑ i, s i = 0) :
    dotProduct w s = dotProduct (center w) s := by
  have hexpand : ∀ i, (center w) i * s i
      = w i * s i - mean w * s i := by
    intro i
    simp only [center, mean]
    ring
  have hsum : ∑ i, (center w) i * s i
      = ∑ i, w i * s i - mean w * ∑ i, s i := by
    calc ∑ i, (center w) i * s i
        = ∑ i, (w i * s i - mean w * s i) :=
          Finset.sum_congr rfl (fun i _ => hexpand i)
      _ = ∑ i, w i * s i - ∑ i, mean w * s i :=
          Finset.sum_sub_distrib _ _
      _ = ∑ i, w i * s i - mean w * ∑ i, s i := by
          rw [Finset.mul_sum]
  show (∑ i, w i * s i) = ∑ i, (center w) i * s i
  rw [hsum, hs, mul_zero, sub_zero]

/-- A linear functional on `Vector n` is pairing with its values on the
standard basis. -/
theorem dual_as_dot {n : Nat} (ψ : (Vector n) →ₗ[ℝ] ℝ) (v : Vector n) :
    ψ v = dotProduct (fun i => ψ (Pi.single i 1)) v := by
  have hexpand : v = ∑ i, Pi.single i (v i) := by
    funext j
    simp only [Finset.sum_apply, Pi.single_apply]
    simp
  have hsingle : ∀ i, Pi.single i (v i)
      = v i • Pi.single i (1 : ℝ) := by
    intro i
    ext j
    by_cases h : j = i <;> simp [h]
  calc ψ v = ψ (∑ i, Pi.single i (v i)) := congrArg ψ hexpand
    _ = ∑ i, ψ (Pi.single i (v i)) := map_sum ψ _ _
    _ = ∑ i, v i * ψ (Pi.single i 1) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hsingle i, map_smul, smul_eq_mul]
    _ = dotProduct (fun i => ψ (Pi.single i 1)) v := by
        show (∑ i, v i * ψ (Pi.single i 1))
          = ∑ i, (fun i => ψ (Pi.single i 1)) i * v i
        refine Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- With no fiber element, `κ` vanishes. -/
theorem kappa_eq_zero_of_no_fiber {d n : Nat} (x : Sample d n)
    (S : Square d)
    (h : ¬ ∃ H : Square d,
      measurementT x H = -center (residual x S)) :
    kappa d n x S = 0 := by
  have hempty : {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨H, -, hHT, -⟩
    exact h ⟨H, hHT⟩
  unfold kappa
  rw [hempty]
  exact Real.sInf_empty

/-- With no observations, every fiber equation is vacuous and `κ` vanishes. -/
theorem kappa_eq_zero_of_n_eq_zero {d n : Nat} (x : Sample d n)
    (S : Square d) (hn : n = 0) : kappa d n x S = 0 := by
  subst hn
  have hmem : (0 : ℝ) ∈ {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} := by
    refine ⟨0, ?_, ?_, matrixOpNorm_zero⟩
    · unfold Matrix.IsSymm
      exact Matrix.transpose_zero
    · funext i
      exact Fin.elim0 i
  have hbdd : BddBelow {r : Real | ∃ H : Square d,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r} := by
    refine ⟨0, ?_⟩
    rintro r ⟨H, -, -, rfl⟩
    exact matrixOpNorm_nonneg H
  have hle : kappa d 0 x S ≤ 0 := by
    unfold kappa
    exact csInf_le hbdd hmem
  have hge : 0 ≤ kappa d 0 x S := by
    unfold kappa
    refine le_csInf ⟨0, hmem⟩ ?_
    rintro r ⟨H, -, -, rfl⟩
    exact matrixOpNorm_nonneg H
  exact le_antisymm hle hge

/-- In dimension zero every matrix is zero and `κ` vanishes. -/
theorem kappa_eq_zero_of_d_eq_zero {d n : Nat} (x : Sample d n)
    (S : Square d) (hd : d = 0) : kappa d n x S = 0 := by
  subst hd
  have hsub : ∀ H : Square 0, H = 0 := by
    intro H
    funext p q
    exact Fin.elim0 p
  have hall : ∀ r ∈ {r : Real | ∃ H : Square 0,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r}, r = 0 := by
    rintro r ⟨H, -, -, hHr⟩
    rw [hsub H, matrixOpNorm_zero] at hHr
    exact hHr.symm
  by_cases hne : {r : Real | ∃ H : Square 0,
      H.IsSymm ∧ measurementT x H = -center (residual x S)
        ∧ matrixOpNorm H = r}.Nonempty
  · have hS : {r : Real | ∃ H : Square 0,
        H.IsSymm ∧ measurementT x H = -center (residual x S)
          ∧ matrixOpNorm H = r} = {0} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨?_, hall⟩
      obtain ⟨r, hr⟩ := hne
      have hr0 : r = 0 := hall r hr
      rw [hr0] at hr
      exact hr
    unfold kappa
    rw [hS]
    exact csInf_singleton 0
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold kappa
    rw [hne]
    exact Real.sInf_empty

section QuotientAssembly

open OpNormInst

/-! ### Range-restricted duality and the quotient bridge -/

/-- Range-restricted measurement operator as a continuous linear map. -/
def measurementTClin {d n : Nat} (x : Sample d n) :
    (Square d) →L[ℝ] ↥(LinearMap.range (measurementTLinear x)) :=
  LinearMap.toContinuousLinearMap
    ((measurementTLinear x).codRestrict
      (LinearMap.range (measurementTLinear x))
      (LinearMap.mem_range_self (measurementTLinear x)))

/-- The range restriction is surjective onto the range. -/
theorem measurementTClin_surjective {d n : Nat} (x : Sample d n) :
    Function.Surjective (measurementTClin x) := by
  intro y
  obtain ⟨H, hH⟩ := LinearMap.mem_range.mp y.2
  exact ⟨H, Subtype.ext hH⟩

/-- Per-sample quotient bound from the mixed-norm body. -/
theorem kappa_le_dualMixed_of_body {d : Nat} (n : Nat → Nat)
    {δ η c : Real} {G : Π d, Set (Sample d (n d))}
    (hBody : MixedNormBody n δ η c G)
    (x : Sample d (n d)) (hx : x ∈ G d) (S : Square d) :
    kappa d (n d) x S
      ≤ c⁻¹ * dualMixed η d (n d) (center (residual x S)) := by
  obtain ⟨hη0, -, hc0, -, hLB⟩ := hBody
  by_cases hd : d = 0
  · rw [kappa_eq_zero_of_d_eq_zero x S hd]
    exact mul_nonneg (inv_nonneg.mpr hc0.le) (dualMixed_nonneg _)
  by_cases hn : n d = 0
  · rw [kappa_eq_zero_of_n_eq_zero x S hn]
    exact mul_nonneg (inv_nonneg.mpr hc0.le) (dualMixed_nonneg _)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hnpos : 0 < n d := Nat.pos_of_ne_zero hn
  set r : Vector (n d) := center (residual x S) with hrdef
  set t : Vector (n d) := -r with htdef
  have hrsum : ∑ i, r i = 0 := sum_center hnpos _
  have htsum : ∑ i, t i = 0 := by simp [htdef, hrsum]
  by_cases hfib : ∃ H : Square d, measurementT x H = t
  · obtain ⟨H0, hH0⟩ := hfib
    have hmem : t ∈ LinearMap.range (measurementTLinear x) :=
      LinearMap.mem_range.mpr ⟨H0, hH0⟩
    have hsurj := measurementTClin_surjective x
    have hnorm := exists_fiber_norming_dual (measurementTClin x) hsurj
      ⟨t, hmem⟩
    obtain ⟨Hmin, φ, hHmin, hmin, hφbound, hφval⟩ := hnorm
    have hMT : measurementT x Hmin = t := congrArg Subtype.val hHmin
    obtain ⟨Hsym, hHsym, hHsymT, -⟩ :=
      exists_symmetric_fiber_le x Hmin t hMT
    have hneS : {r : Real | ∃ H : Square d,
        H.IsSymm ∧ measurementT x H = t
          ∧ matrixOpNorm H = r}.Nonempty :=
      ⟨matrixOpNorm Hsym, Hsym, hHsym, hHsymT, rfl⟩
    have hkappa : kappa d (n d) x S ≤ matrixOpNorm Hmin := by
      have h1 : kappa d (n d) x S ≤ sInf {r : Real | ∃ H : Square d,
          measurementT x H = t ∧ matrixOpNorm H = r} :=
        kappa_le_sInf_full x S hneS
      have hbdd : BddBelow {r : Real | ∃ H : Square d,
          measurementT x H = t ∧ matrixOpNorm H = r} := by
        refine ⟨0, ?_⟩
        rintro r ⟨H, -, rfl⟩
        exact matrixOpNorm_nonneg H
      have hmem : matrixOpNorm Hmin ∈ {r : Real | ∃ H : Square d,
          measurementT x H = t ∧ matrixOpNorm H = r} :=
        ⟨Hmin, hMT, rfl⟩
      exact le_trans h1 (csInf_le hbdd hmem)
    obtain ⟨ψ, hψext, -⟩ := exists_extension_norm_eq _ φ
    set w : Vector (n d) := fun i => ψ.toLinearMap (Pi.single i 1)
      with hwdef
    set wbar : Vector (n d) := center w with hwbardef
    have hwbar0 : ∑ i, wbar i = 0 := sum_center hnpos _
    have hφt : φ ⟨t, hmem⟩ = dotProduct wbar t := by
      have e1 : φ ⟨t, hmem⟩ = ψ t := (hψext _).symm
      have e2 : ψ t = dotProduct w t := dual_as_dot ψ.toLinearMap t
      have e3 : dotProduct w t = dotProduct wbar t :=
        dot_center_right w t htsum
      rw [e1, e2]
      exact e3
    have hnuc : nuclearNorm (centeredAdjoint x wbar) ≤ 1 := by
      unfold nuclearNorm
      refine csSup_le (nuclearNorm_nonempty _) ?_
      rintro s ⟨U, hU, rfl⟩
      have eU : (∑ i, ∑ j, U i j * (centeredAdjoint x wbar) i j)
          = (φ.comp (measurementTClin x)) U := by
        have a1 : (φ.comp (measurementTClin x)) U
            = φ (measurementTClin x U) := rfl
        have a2 : φ (measurementTClin x U) = ψ (measurementT x U) :=
          (hψext _).symm
        have a3 : ψ (measurementT x U)
            = dotProduct w (measurementT x U) :=
          dual_as_dot ψ.toLinearMap _
        have a4 : dotProduct w (measurementT x U)
            = dotProduct wbar (measurementT x U) :=
          dot_center_right w _ (measurementT_sum_zero hnpos x U)
        have a5 : dotProduct wbar (measurementT x U)
            = dotProduct (measurementT x U) wbar :=
          dotProduct_comm _ _
        have a6 : dotProduct (measurementT x U) wbar
            = ∑ i, ∑ j, U i j * (centeredAdjoint x wbar) i j :=
          adjoint_identity x U wbar hwbar0
        rw [a1, a2, a3, a4, a5, a6]
      rw [eU]
      calc (φ.comp (measurementTClin x)) U
          ≤ ‖(φ.comp (measurementTClin x)) U‖ := by
            rw [Real.norm_eq_abs]
            exact le_abs_self _
        _ ≤ ‖φ.comp (measurementTClin x)‖ * ‖U‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * 1 :=
            mul_le_mul hφbound hU (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hN : mixedNorm η d (n d) wbar
        ≤ c⁻¹ * nuclearNorm (centeredAdjoint x wbar) := by
      have hLBw := hLB d x hx wbar hwbar0
      have hle : mixedNorm η d (n d) wbar
          ≤ nuclearNorm (centeredAdjoint x wbar) / c :=
        (le_div_iff₀ hc0).mpr (by rw [mul_comm]; exact hLBw)
      rwa [div_eq_inv_mul] at hle
    have hhold := mixedNorm_holder (η := η) (e := r) (y := wbar)
      hη0 hdpos
    have hdot : dotProduct wbar t = -(∑ i, r i * wbar i) := by
      show (∑ i, wbar i * t i) = _
      simp only [htdef, Pi.neg_apply, mul_neg]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_comm (wbar i) (r i)]
    calc kappa d (n d) x S ≤ matrixOpNorm Hmin := hkappa
      _ = ‖Hmin‖ := rfl
      _ = φ ⟨t, hmem⟩ := hφval.symm
      _ = dotProduct wbar t := hφt
      _ ≤ |dotProduct wbar t| := le_abs_self _
      _ = |∑ i, r i * wbar i| := by rw [hdot, abs_neg]
      _ ≤ dualMixed η d (n d) r * mixedNorm η d (n d) wbar := hhold
      _ ≤ dualMixed η d (n d) r
            * (c⁻¹ * nuclearNorm (centeredAdjoint x wbar)) :=
          mul_le_mul_of_nonneg_left hN (dualMixed_nonneg _)
      _ ≤ dualMixed η d (n d) r * (c⁻¹ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnuc
              (inv_nonneg.mpr hc0.le)) (dualMixed_nonneg _)
      _ = c⁻¹ * dualMixed η d (n d) r := by ring
  · have h0 : kappa d (n d) x S = 0 :=
      kappa_eq_zero_of_no_fiber x S hfib
    rw [h0]
    exact mul_nonneg (inv_nonneg.mpr hc0.le) (dualMixed_nonneg _)

/-- Section 12 bridge (B2): the mixed-norm bound implies the quotient
bound. -/
theorem quotientBridge_theorem : QuotientBridge := by
  unfold QuotientBridge QuotientBody
  intro n δ η c G Sstar hBody d x hx
  exact kappa_le_dualMixed_of_body n hBody x hx (Sstar d x)

end QuotientAssembly

end GaussianEllipsoid
