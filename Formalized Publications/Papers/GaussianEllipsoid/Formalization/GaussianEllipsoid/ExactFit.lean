/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.

Kernel-checked exact-fit correction algebra on the actual coordinate matrices from Basic.lean.
Source: paper.tex, Section 2 and Section 7 (exact correction).
-/
import GaussianEllipsoid.Centering
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic

noncomputable section

namespace GaussianEllipsoid

/-- Linearity of quadratic measurement in its matrix argument. -/
theorem quadratic_add {d : Nat} (S H : Square d) (v : Vector d) :
    quadratic (S + H) v = quadratic S v + quadratic H v := by
  simp only [quadratic, Matrix.add_mulVec, dotProduct_add]

/-- The actual measurement vector is additive. -/
theorem measurementA_add {d n : Nat} (x : Sample d n) (S H : Square d) :
    measurementA x (S + H) = measurementA x S + measurementA x H := by
  funext i
  exact quadratic_add S H (x i)

/-- The centered measurement map is additive, including dimension zero. -/
theorem measurementT_add {d n : Nat} (x : Sample d n) (S H : Square d) :
    measurementT x (S + H) = measurementT x S + measurementT x H := by
  unfold measurementT
  rw [measurementA_add, center_add]
  funext i
  exact add_div _ _ _

/-- Positive semidefiniteness implies nonnegative coordinate measurements. -/
theorem quadratic_nonneg {d : Nat} {S : Square d}
    (hS : S.PosSemidef) (v : Vector d) : 0 <= quadratic S v := by
  simpa [quadratic] using hS.dotProduct_mulVec_nonneg v

/-- A zero quadratic measurement for a PSD matrix is exactly a kernel vector. -/
theorem quadratic_eq_zero_iff_mulVec_eq_zero {d : Nat} {S : Square d}
    (hS : S.PosSemidef) (v : Vector d) :
    quadratic S v = 0 <-> Matrix.mulVec S v = 0 := by
  simpa [quadratic] using hS.dotProduct_mulVec_zero_iff v

/-- If every observation lies in the kernel of S, then S annihilates their Gram sum. -/
theorem mul_gram_eq_zero_of_mulVec_eq_zero {d n : Nat}
    (x : Sample d n) (S : Square d)
    (hkernel : forall i, Matrix.mulVec S (x i) = 0) :
    S * gram x = 0 := by
  unfold gram
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Matrix.mul_vecMulVec, hkernel i]
  ext j k
  simp [Matrix.vecMulVec]

/-- A rank-one matrix acts by its ordinary real dot product. -/
theorem rank_one_mulVec {d : Nat} (v w : Vector d) :
    Matrix.mulVec (Matrix.vecMulVec v v) w = (dotProduct v w) • v := by
  funext j
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul]
  simp_rw [mul_assoc]
  rw [<- Finset.mul_sum, mul_comm]

/-- The actual sample Gram map is a linear combination of the observed vectors. -/
theorem gram_mulVec_eq_sum {d n : Nat} (x : Sample d n) (v : Vector d) :
    Matrix.mulVec (gram x) v =
      Finset.univ.sum (fun i => (dotProduct (x i) v) • (x i)) := by
  simp only [gram, Matrix.sum_mulVec, rank_one_mulVec]

/-- The Gram quadratic form is the sum of the squared sample inner products. -/
theorem quadratic_gram {d n : Nat} (x : Sample d n) (v : Vector d) :
    quadratic (gram x) v = Finset.univ.sum (fun i => (dotProduct (x i) v) ^ 2) := by
  rw [quadratic, gram_mulVec_eq_sum, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm v (x i)]
  ring

/-- Every actual sample Gram sum is positive semidefinite. -/
theorem gram_posSemidef {d n : Nat} (x : Sample d n) : (gram x).PosSemidef := by
  have : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  unfold gram
  apply Matrix.posSemidef_sum
  intro i hi
  simpa using Matrix.posSemidef_vecMulVec_self_star (x i)

/-- The Gram matrix is PD precisely when the actual observations span the ambient
real vector space. This is a deterministic bridge, without an a.s. Gaussian claim. -/
theorem gram_posDef_iff_span_eq_top {d n : Nat} (x : Sample d n) :
    (gram x).PosDef <-> Submodule.span Real (Set.range x) = (Top.top : Submodule Real (Vector d)) := by
  constructor
  case mp =>
    intro hGram
    have hsurj : Function.Surjective (Matrix.mulVec (gram x)) :=
      Matrix.mulVec_surjective_iff_isUnit.mpr hGram.isUnit
    apply top_unique
    intro v hv
    apply Exists.elim (hsurj v)
    intro w hw
    rw [<- hw, gram_mulVec_eq_sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self i)
  case mpr =>
    intro hspan
    apply (posDef_iff_coordinates (gram x)).mpr
    refine And.intro ((hermitian_iff_symmetric (gram x)).mp
      (gram_posSemidef x).isHermitian) ?_
    intro v hv
    have hnonneg := quadratic_nonneg (gram_posSemidef x) v
    have hnonzero : Not (quadratic (gram x) v = 0) := by
      intro hzero
      have hsum : Finset.univ.sum (fun i => (dotProduct (x i) v) ^ 2) = 0 := by
        rwa [quadratic_gram] at hzero
      have hall : forall i, dotProduct (x i) v = 0 := by
        intro i
        have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (dotProduct (x j) v))).mp hsum i (Finset.mem_univ i)
        nlinarith
      have hvspan : Membership.mem (Submodule.span Real (Set.range x)) v := by
        rw [hspan]
        trivial
      have hvv : dotProduct v v = 0 := by
        refine Submodule.span_induction
          (p := fun w _ => dotProduct w v = 0) ?hmem ?hzero ?hadd ?hsmul hvspan
        case hmem =>
          intro w hw
          apply Exists.elim hw
          intro i hi
          rw [<- hi]
          exact hall i
        case hzero =>
          exact zero_dotProduct v
        case hadd =>
          intro a b ha hb hda hdb
          rw [add_dotProduct, hda, hdb, add_zero]
        case hsmul =>
          intro a w hw hdw
          rw [smul_dotProduct, hdw, smul_zero]
      exact hv (dotProduct_self_eq_zero.mp hvv)
    exact lt_of_le_of_ne hnonneg (Ne.symm hnonzero)

/-- A PD sample Gram sum prevents a nonzero PSD matrix from vanishing on every sample. -/
theorem eq_zero_of_zero_measurements {d n : Nat} {x : Sample d n} {S : Square d}
    (hS : S.PosSemidef) (hGram : (gram x).PosDef)
    (hzero : forall i, quadratic S (x i) = 0) : S = 0 := by
  have hkernel : forall i, Matrix.mulVec S (x i) = 0 :=
    fun i => (quadratic_eq_zero_iff_mulVec_eq_zero hS (x i)).mp (hzero i)
  have hprod : S * gram x = 0 := mul_gram_eq_zero_of_mulVec_eq_zero x S hkernel
  obtain ⟨u, hu⟩ := hGram.isUnit
  rw [← hu] at hprod
  have h2 : S * ((u * u⁻¹ : (Square d)ˣ) : Square d) = 0 := by
    rw [Units.val_mul, ← mul_assoc, hprod, zero_mul]
  rwa [mul_inv_cancel, Units.val_one, mul_one] at h2

/-- The common value is strictly positive; no separate n >= d assumption is needed
once the actual sample Gram sum is assumed positive definite. -/
theorem common_value_pos {d n : Nat} (hn : 0 < n)
    {x : Sample d n} {S : Square d} {c : Real}
    (hS : S.PosSemidef) (hne : Not (S = 0)) (hGram : (gram x).PosDef)
    (hcommon : forall i, quadratic S (x i) = c) : 0 < c := by
  have hc : 0 <= c := by
    rw [<- hcommon (Fin.mk 0 hn)]
    exact quadratic_nonneg hS _
  have hcne : Not (c = 0) := by
    intro hz
    apply hne
    apply eq_zero_of_zero_measurements hS hGram
    intro i
    exact (hcommon i).trans hz
  exact lt_of_le_of_ne hc (Ne.symm hcne)

/-- Centering Q and centering A have identical kernels, with the literal sqrt(2)
normalization retained. -/
theorem center_measurementQ_eq_zero_iff {d n : Nat} (hn : 0 < n)
    (x : Sample d n) (S : Square d) :
    center (measurementQ x S) = 0 <-> center (measurementA x S) = 0 := by
  have hsqrt : Not (Real.sqrt 2 = 0) := by positivity
  rw [center_measurementQ hn]
  constructor
  case mp =>
    intro h
    funext i
    have hi := congrFun h i
    change center (measurementA x S) i / Real.sqrt 2 = 0 at hi
    exact (div_eq_zero_iff.mp hi).resolve_right hsqrt
  case mpr =>
    intro h
    funext i
    simp [h]

/-- In positive dimension, T has the same kernel as the centering of A. -/
theorem measurementT_eq_zero_iff {d n : Nat} (hd : 0 < d)
    (x : Sample d n) (S : Square d) :
    measurementT x S = 0 <-> center (measurementA x S) = 0 := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hsqrt : Not (Real.sqrt (d : Real) = 0) := ne_of_gt (Real.sqrt_pos.2 hdR)
  constructor
  case mp =>
    intro h
    funext i
    have hi := congrFun h i
    change center (measurementA x S) i / Real.sqrt (d : Real) = 0 at hi
    exact (div_eq_zero_iff.mp hi).resolve_right hsqrt
  case mpr =>
    intro h
    funext i
    simp [measurementT, h]

/-- Centered Q vanishes precisely when all literal quadratic measurements agree. -/
theorem center_measurementQ_eq_zero_iff_common {d n : Nat} (hn : 0 < n)
    (x : Sample d n) (S : Square d) :
    center (measurementQ x S) = 0 <->
      exists c : Real, forall i, quadratic S (x i) = c := by
  rw [center_measurementQ_eq_zero_iff hn, center_eq_zero_iff_constant hn]
  rfl

/-- Every feasible matrix belongs to the actual centered kernel. -/
theorem Feasible.center_measurementQ_eq_zero {d n : Nat} (hn : 0 < n)
    {x : Sample d n} {S : Square d} (h : Feasible x S) :
    center (measurementQ x S) = 0 := by
  apply (center_measurementQ_eq_zero_iff_common hn x S).mpr
  exact Exists.intro (d : Real) h.2

/-- Exact rescaling of a nonzero PSD matrix in the centered kernel. -/
theorem hasFit_of_nonzero_psd_centered_kernel {d n : Nat} (hn : 0 < n)
    {x : Sample d n} {S : Square d}
    (hS : S.PosSemidef) (hne : Not (S = 0)) (hGram : (gram x).PosDef)
    (hkernel : center (measurementQ x S) = 0) : HasFit x := by
  apply Exists.elim ((center_measurementQ_eq_zero_iff_common hn x S).mp hkernel)
  intro c hcommon
  have hc := common_value_pos hn hS hne hGram hcommon
  exact Exists.intro ((((d : Real) / c)) • S)
    (feasible_of_positive_common_value hS hc hcommon)

/-- The full deterministic centered-kernel equivalence used above the threshold. -/
theorem hasFit_iff_nonzero_psd_centered_kernel {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n} (hGram : (gram x).PosDef) :
    HasFit x <-> exists S : Square d,
      S.PosSemidef /\ Not (S = 0) /\ center (measurementQ x S) = 0 := by
  constructor
  case mp =>
    intro h
    apply Exists.elim h
    intro S hS
    exact Exists.intro S (And.intro hS.1
      (And.intro (hS.ne_zero hd hn) (hS.center_measurementQ_eq_zero hn)))
  case mpr =>
    intro h
    apply Exists.elim h
    intro S hS
    exact hasFit_of_nonzero_psd_centered_kernel hn hS.1 hS.2.1 hGram hS.2.2

/-- Absence of nonzero PSD matrices in the centered kernel excludes a fit. -/
theorem not_hasFit_of_centered_kernel_trivial {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n}
    (htrivial : forall S : Square d,
      S.PosSemidef -> center (measurementQ x S) = 0 -> S = 0) :
    Not (HasFit x) := by
  intro h
  apply Exists.elim h
  intro S hS
  exact hS.ne_zero hd hn (htrivial S hS.1 (hS.center_measurementQ_eq_zero hn))

/-- Positive definiteness in a positive dimension excludes the zero matrix. -/
theorem posDef_ne_zero {d : Nat} (hd : 0 < d) {S : Square d}
    (hS : S.PosDef) : Not (S = 0) := by
  intro hz
  have hp := hS.diag_pos (i := Fin.mk 0 hd)
  simp [hz] at hp

/-- A PD matrix with centered measurements zero can be rescaled to a strict fit. -/
theorem hasStrictFit_of_posDef_centered_kernel {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n} {S : Square d}
    (hS : S.PosDef) (hGram : (gram x).PosDef)
    (hkernel : center (measurementA x S) = 0) : HasStrictFit x := by
  apply Exists.elim ((center_eq_zero_iff_constant hn (measurementA x S)).mp hkernel)
  intro c hcommon
  have hc := common_value_pos hn hS.posSemidef (posDef_ne_zero hd hS) hGram hcommon
  exact Exists.intro ((((d : Real) / c)) • S)
    (strictlyFeasible_of_positive_common_value hd hS hc hcommon)

/-- For a PD matrix, one nonzero observed vector already makes its common
quadratic measurement strictly positive. -/
theorem common_value_pos_of_posDef {d n : Nat} {x : Sample d n}
    {S : Square d} {c : Real} (hS : S.PosDef) (i : Fin n)
    (hxi : Not (x i = 0)) (hcommon : forall j, quadratic S (x j) = c) : 0 < c := by
  have hp : 0 < quadratic S (x i) := by
    simpa [quadratic] using hS.dotProduct_mulVec_pos hxi
  rwa [hcommon i] at hp

/-- Strict exactification at the sample level needs only one nonzero observation,
not positive definiteness of the entire Gram sum. The explicit rescaling is exposed. -/
theorem strictFit_rescaling_of_centered_kernel {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n} {S : Square d}
    (hS : S.PosDef) (i : Fin n) (hxi : Not (x i = 0))
    (hkernel : center (measurementA x S) = 0) :
    exists c : Real, 0 < c /\ StrictlyFeasible x ((((d : Real) / c)) • S) := by
  apply Exists.elim ((center_eq_zero_iff_constant hn (measurementA x S)).mp hkernel)
  intro c hcommon
  have hc := common_value_pos_of_posDef hS i hxi hcommon
  exact Exists.intro c (And.intro hc
    (strictlyFeasible_of_positive_common_value hd hS hc hcommon))

/-- Solving the literal correction equation removes the centered residual. -/
theorem correction_eq_implies_measurementT_eq_zero {d n : Nat} (hn : 0 < n)
    {x : Sample d n} {S H : Square d}
    (hcorr : measurementT x H = -center (residual x S)) :
    measurementT x (S + H) = 0 := by
  rw [measurementT_add, hcorr, center_residual_eq_measurementT hn]
  exact add_neg_cancel _

/-- Deterministic exactification: a positive definite correction is rescaled to
an actual strict fit. The probabilistic existence and norm bound for H are separate. -/
theorem hasStrictFit_of_correction {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    {x : Sample d n} {S H : Square d} (hGram : (gram x).PosDef)
    (hPD : (S + H).PosDef)
    (hcorr : measurementT x H = -center (residual x S)) : HasStrictFit x := by
  apply hasStrictFit_of_posDef_centered_kernel hd hn hPD hGram
  apply (measurementT_eq_zero_iff hd x (S + H)).mp
  exact correction_eq_implies_measurementT_eq_zero hn hcorr

/-- The exact correction and rescaling step under the weaker nonzero-sample
condition used by the manuscript's Section 7. -/
theorem hasStrictFit_of_correction_at_nonzero_sample {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n} {S H : Square d}
    (hPD : (S + H).PosDef) (i : Fin n) (hxi : Not (x i = 0))
    (hcorr : measurementT x H = -center (residual x S)) : HasStrictFit x := by
  have hcenter : center (measurementA x (S + H)) = 0 :=
    (measurementT_eq_zero_iff hd x (S + H)).mp
      (correction_eq_implies_measurementT_eq_zero hn hcorr)
  apply Exists.elim (strictFit_rescaling_of_centered_kernel hd hn hPD i hxi hcenter)
  intro c hc
  exact Exists.intro ((((d : Real) / c)) • (S + H)) hc.2

/-- A coordinate version of spectral-gap preservation, retaining the actual
quadratic forms. A norm-to-quadratic estimate supplies hH in the paper. -/
theorem posDef_add_of_quadratic_bounds {d : Nat} {S H : Square d}
    {lower error : Real} (hSym : (S + H).IsSymm) (hgap : error < lower)
    (hS : forall v : Vector d, lower * dotProduct v v <= quadratic S v)
    (hH : forall v : Vector d, abs (quadratic H v) <= error * dotProduct v v) :
    (S + H).PosDef := by
  apply (posDef_iff_coordinates (S + H)).mpr
  refine And.intro hSym ?_
  intro v hv
  have hnorm : 0 < dotProduct v v := by
    simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hv)
  have hlow := hS v
  have herr := (abs_le.mp (hH v)).1
  rw [quadratic_add]
  nlinarith [mul_pos (sub_pos.mpr hgap) hnorm]

/-- Exactification with the positive-definiteness proof supplied by explicit
quadratic estimates, rather than assumed for the corrected matrix. -/
theorem hasStrictFit_of_quadratic_correction_bounds {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) {x : Sample d n} {S H : Square d}
    {lower error : Real} (hSym : (S + H).IsSymm) (hgap : error < lower)
    (hS : forall v : Vector d, lower * dotProduct v v <= quadratic S v)
    (hH : forall v : Vector d, abs (quadratic H v) <= error * dotProduct v v)
    (i : Fin n) (hxi : Not (x i = 0))
    (hcorr : measurementT x H = -center (residual x S)) : HasStrictFit x := by
  exact hasStrictFit_of_correction_at_nonzero_sample hd hn
    (posDef_add_of_quadratic_bounds hSym hgap hS hH) i hxi hcorr

/-- Trace pairing with an actual rank-one sample matrix is its quadratic measurement. -/
theorem trace_mul_rank_one {d : Nat} (S : Square d) (v : Vector d) :
    Matrix.trace (S * Matrix.vecMulVec v v) = quadratic S v := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact dotProduct_comm _ _

/-- Literal trace pairing with the coordinate formula for the adjoint. -/
theorem trace_mul_centeredAdjoint {d n : Nat}
    (x : Sample d n) (S : Square d) (y : Vector n) :
    Matrix.trace (S * centeredAdjoint x y) =
      (1 / Real.sqrt (d : Real)) *
        Finset.univ.sum (fun i => y i * quadratic S (x i)) := by
  simp only [centeredAdjoint, mul_smul_comm, Matrix.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum, trace_mul_rank_one, smul_eq_mul]

/-- The stated adjoint formula is the actual trace adjoint on the zero-sum subspace. -/
theorem measurementT_adjoint_identity {d n : Nat}
    (x : Sample d n) (S : Square d) (y : Vector n)
    (hy : Finset.univ.sum (fun i => y i) = 0) :
    dotProduct y (measurementT x S) = Matrix.trace (S * centeredAdjoint x y) := by
  have hdivide : dotProduct y (measurementT x S) =
      dotProduct y (center (measurementA x S)) / Real.sqrt (d : Real) := by
    simp [dotProduct, measurementT, mul_div_assoc, Finset.sum_div]
  rw [hdivide, dotProduct_center_right, hy, mul_zero, sub_zero,
    trace_mul_centeredAdjoint]
  simp only [dotProduct, measurementA]
  ring

/-- On zero-sum coefficients the identity-matrix terms cancel exactly. -/
theorem centeredAdjoint_eq_centered_rank_one_sum {d n : Nat}
    (x : Sample d n) (y : Vector n)
    (hy : Finset.univ.sum (fun i => y i) = 0) :
    centeredAdjoint x y = (1 / Real.sqrt (d : Real)) •
      (Finset.univ.sum fun i =>
        (y i) • (Matrix.vecMulVec (x i) (x i) - (1 : Square d))) := by
  unfold centeredAdjoint
  congr 1
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  have hsum1 : (Finset.univ.sum fun i => (y i) • (1 : Square d)) = 0 := by
    simp only [Algebra.smul_def, mul_one]
    rw [← map_sum (algebraMap ℝ (Square d)) (fun i => y i) Finset.univ, hy, map_zero]
  rw [hsum1, sub_zero]

/-- The adjoint of the zero weight vector vanishes. -/
theorem centeredAdjoint_zero {d n : Nat} (x : Sample d n) :
    centeredAdjoint x 0 = 0 := by
  simp [centeredAdjoint]

/-- The adjoint is additive in the weight vector. -/
theorem centeredAdjoint_add {d n : Nat} (x : Sample d n)
    (y₁ y₂ : Vector n) :
    centeredAdjoint x (y₁ + y₂)
      = centeredAdjoint x y₁ + centeredAdjoint x y₂ := by
  unfold centeredAdjoint
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

/-- The adjoint is homogeneous in the weight vector. -/
theorem centeredAdjoint_smul {d n : Nat} (x : Sample d n)
    (c : ℝ) (y : Vector n) :
    centeredAdjoint x (c • y) = c • centeredAdjoint x y := by
  unfold centeredAdjoint
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- The adjoint is a symmetric matrix (each rank-one summand is). -/
theorem centeredAdjoint_symm {d n : Nat} (x : Sample d n) (y : Vector n) :
    (centeredAdjoint x y).IsSymm := by
  unfold centeredAdjoint Matrix.IsSymm
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- Subtracting matrices subtracts their actual quadratic measurements. -/
theorem quadratic_sub {d : Nat} (S H : Square d) (v : Vector d) :
    quadratic (S - H) v = quadratic S v - quadratic H v := by
  simp only [quadratic, Matrix.sub_mulVec, dotProduct_sub]

/-- The identity matrix has the ordinary squared Euclidean quadratic form. -/
theorem quadratic_one {d : Nat} (v : Vector d) :
    quadratic (1 : Square d) v = dotProduct v v := by
  simp only [quadratic, Matrix.one_mulVec]

/-- Quantitative lower bound for every corrected quadratic form. -/
theorem quadratic_add_lower_bound {d : Nat} {S H : Square d}
    {lower error : Real}
    (hS : forall v : Vector d, lower * dotProduct v v <= quadratic S v)
    (hH : forall v : Vector d, abs (quadratic H v) <= error * dotProduct v v)
    (v : Vector d) :
    (lower - error) * dotProduct v v <= quadratic (S + H) v := by
  have hlow := hS v
  have herr := (abs_le.mp (hH v)).1
  rw [quadratic_add]
  nlinarith

/-- The lower-gap estimate stated as actual positive semidefiniteness of a
matrix difference, giving the paper's Loewner-order conclusion in coordinates. -/
theorem corrected_gap_posSemidef {d : Nat} {S H : Square d}
    {lower error : Real} (hSym : (S + H).IsSymm)
    (hS : forall v : Vector d, lower * dotProduct v v <= quadratic S v)
    (hH : forall v : Vector d, abs (quadratic H v) <= error * dotProduct v v) :
    (S + H - ((lower - error)) • (1 : Square d)).PosSemidef := by
  apply (posSemidef_iff_coordinates _).mpr
  refine And.intro (hSym.sub (Matrix.isSymm_one.smul (lower - error))) ?_
  intro v
  rw [quadratic_sub, quadratic_smul, quadratic_one]
  have hbound := quadratic_add_lower_bound hS hH v
  linarith

/-- Exact half-gap conclusion of the final correction step, after converting
the paper's operator-norm hypothesis to the displayed quadratic bound. -/
theorem corrected_half_gap_posSemidef {d : Nat} {S H : Square d}
    {lower : Real} (hSym : (S + H).IsSymm)
    (hS : forall v : Vector d, lower * dotProduct v v <= quadratic S v)
    (hH : forall v : Vector d, abs (quadratic H v) <= (lower / 2) * dotProduct v v) :
    (S + H - ((lower / 2)) • (1 : Square d)).PosSemidef := by
  have h := corrected_gap_posSemidef hSym hS hH
  have he : lower - lower / 2 = lower / 2 := by ring
  rw [he] at h
  exact h

end GaussianEllipsoid
