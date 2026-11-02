import PaperSymmetricSteinSource

/-! New reconstruction of the manuscript's literal tensor contraction.
The contraction is defined by S_ab and B_a(w), not by the desired coordinate
identity. Source: immutable final manuscript lines 4040--4107. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open BMQuadraticStein PaperSymmetricDirections PaperSymmetricBasis
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperSymmetricPullback
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

variable {d : ℕ}

def sourceSMatrix (a b : Fin d) : Square d := fun i j =>
  ((if i=a ∧ j=b then 1 else 0) + (if i=b ∧ j=a then 1 else 0)) / 2

def sourceBMatrix (a : Fin d) (w : Fin d → ℝ) : Square d := fun i j =>
  ((if i=a then w j else 0) + (if j=a then w i else 0)) / Real.sqrt 2

lemma sourceSMatrix_transpose (a b : Fin d) : (sourceSMatrix a b).transpose = sourceSMatrix a b := by
  ext i j
  simp [sourceSMatrix, Matrix.transpose_apply, and_comm, add_comm]

lemma sourceBMatrix_transpose (a : Fin d) (w : Fin d → ℝ) :
    (sourceBMatrix a w).transpose = sourceBMatrix a w := by
  ext i j
  simp only [sourceBMatrix, Matrix.transpose_apply]
  ring

def sourceS (a b : Fin d) : SymFrob d := ofMatrix (sourceSMatrix a b) (sourceSMatrix_transpose a b)
def sourceB (a : Fin d) (w : Fin d → ℝ) : SymFrob d :=
  ofMatrix (sourceBMatrix a w) (sourceBMatrix_transpose a w)

def tri (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (U V W : SymFrob d) : ℝ := T (Fin.cons U (Fin.cons V (Fin.cons W Fin.elim0)))

/-- Literal manuscript contraction (1/sqrt(2)) sum_ab T[B_a,B_b,S_ab]. -/
def sourceTensorCorrection (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (w : Fin d → ℝ) : ℝ :=
  (1 / Real.sqrt 2) * ∑ i : Fin d, ∑ j : Fin d,
    tri T (sourceB i w) (sourceB j w) (sourceS i j)

lemma sourceS_coordinate (i j : Fin d) (a : Index d) :
    coordinates (sourceS i j) a = qMatrix a i j := by
  have hsym (k l : Fin d) : qMatrix a l k = qMatrix a k l :=
    congrFun (congrFun (Q_transpose a.val.1 a.val.2) k) l
  unfold coordinates sourceS
  rw [matrix_ofMatrix]
  change (∑ k, ∑ l, sourceSMatrix i j k l * qMatrix a k l) = _
  simp only [sourceSMatrix, add_div, add_mul, div_mul_eq_mul_div,
    Finset.sum_add_distrib, ← Finset.sum_div, ite_mul, one_mul, zero_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [hsym]
  ring

lemma sourceB_coordinate (i : Fin d) (w : Fin d → ℝ) (a : Index d) :
    coordinates (sourceB i w) a = Real.sqrt 2 * ∑ j, qMatrix a i j * w j := by
  have hsym (k l : Fin d) : qMatrix a l k = qMatrix a k l :=
    congrFun (congrFun (Q_transpose a.val.1 a.val.2) k) l
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold coordinates sourceB
  rw [matrix_ofMatrix]
  change (∑ k, ∑ l, sourceBMatrix i w k l * qMatrix a k l) = _
  simp only [sourceBMatrix, add_div, add_mul, div_mul_eq_mul_div,
    Finset.sum_add_distrib, ← Finset.sum_div, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [← add_div]
  simp_rw [hsym, mul_comm (w _)]
  have hscale : (1 / Real.sqrt 2) + (1 / Real.sqrt 2) = Real.sqrt 2 := by
    field_simp
    nlinarith [hs]
  calc
    _ = ((1 / Real.sqrt 2) + (1 / Real.sqrt 2)) * (∑ j, qMatrix a i j*w j) := by ring
    _ = _ := by rw [hscale]

lemma tri_sum_first {I : Type*} [Fintype I]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (r : I → ℝ) (U : I → SymFrob d) (V W : SymFrob d) :
    tri T (∑ i, r i • U i) V W = ∑ i, r i * tri T (U i) V W := by
  change (T.curryLeft (∑ i, r i • U i)) (Fin.cons V (Fin.cons W Fin.elim0)) = _
  simp only [map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.curryLeft_apply, tri]

lemma tri_sum_second {I : Type*} [Fintype I]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (U : SymFrob d) (r : I → ℝ) (V : I → SymFrob d) (W : SymFrob d) :
    tri T U (∑ i, r i • V i) W = ∑ i, r i * tri T U (V i) W := by
  change ((T.curryLeft U).curryLeft (∑ i, r i • V i)) (Fin.cons W Fin.elim0) = _
  simp only [map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.curryLeft_apply, tri]

lemma tri_sum_third {I : Type*} [Fintype I]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (U V : SymFrob d) (r : I → ℝ) (W : I → SymFrob d) :
    tri T U V (∑ i, r i • W i) = ∑ i, r i * tri T U V (W i) := by
  change (((T.curryLeft U).curryLeft V).curryLeft (∑ i, r i • W i)) Fin.elim0 = _
  simp only [map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.curryLeft_apply, tri]

/-- Trilinearity gives the full ordered coordinate expansion before the
manuscript contraction coefficient is collected. -/
lemma tri_coordinates (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ)
    (U V W : SymFrob d) :
    tri T U V W = ∑ c : Index d, ∑ b : Index d, ∑ a : Index d,
      coordinates U c * coordinates V b * coordinates W a *
        tri T (qSym d c) (qSym d b) (qSym d a) := by
  have hU : tri T U V W = ∑ c : Index d, coordinates U c * tri T (qSym d c) V W := by
    conv_lhs => rw [← synth_coordinates U, synth_apply]
    exact tri_sum_first T _ _ V W
  rw [hU]
  apply Finset.sum_congr rfl
  intro c _
  have hV : tri T (qSym d c) V W =
      ∑ b : Index d, coordinates V b * tri T (qSym d c) (qSym d b) W := by
    conv_lhs => rw [← synth_coordinates V, synth_apply]
    exact tri_sum_second T _ _ _ W
  rw [hV, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hW : tri T (qSym d c) (qSym d b) W =
      ∑ a : Index d, coordinates W a * tri T (qSym d c) (qSym d b) (qSym d a) := by
    conv_lhs => rw [← synth_coordinates W, synth_apply]
    exact tri_sum_third T _ _ _ _
  rw [hW]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma qMatrix_trace (a b : Index d) :
    Matrix.trace (qMatrix a*qMatrix b) = if a=b then 1 else 0 := by
  change Matrix.trace (Q a.val.1 a.val.2 * Q b.val.1 b.val.2) = _
  rw [← GaussianEllipsoid.PaperWickAdapter.frobenius_pairing_eq_trace _ _
    (Q_transpose b.val.1 b.val.2)]
  change frobInner (Q a.val.1 a.val.2) (Q b.val.1 b.val.2) = _
  rw [Q_gram _ _ _ _ a.property b.property]
  congr 1
  exact propext (by simp only [Subtype.ext_iff, Prod.ext_iff])

lemma source_coefficient (w : Fin d → ℝ) (a b c : Index d) :
    (1 / Real.sqrt 2) * (∑ i : Fin d, ∑ j : Fin d,
      coordinates (sourceB i w) c * coordinates (sourceB j w) b *
        coordinates (sourceS i j) a) =
      Real.sqrt 2 * MvPolynomial.eval w (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) := by
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hA : (qMatrix a).transpose = qMatrix a := Q_transpose _ _
  have hB : (qMatrix b).transpose = qMatrix b := Q_transpose _ _
  have hsym (i j : Fin d) : qMatrix a j i = qMatrix a i j := congrFun (congrFun hA i) j
  let u := (qMatrix b).mulVec w
  let v := (qMatrix c).mulVec w
  have he : (∑ i, ∑ j, v i*u j*qMatrix a i j) =
      dotProduct u ((qMatrix a).mulVec v) := by
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym]
    ring
  have hd : dotProduct u ((qMatrix a).mulVec v) =
      dotProduct w ((qMatrix b*qMatrix a*qMatrix c).mulVec w) := by
    dsimp [u, v]
    rw [← Matrix.vecMul_transpose, hB, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hp : dotProduct w ((qMatrix b*qMatrix a*qMatrix c).mulVec w) =
      MvPolynomial.eval w (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) := by
    simp only [rawQuadratic, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [sourceB_coordinate, sourceS_coordinate]
  change (1 / Real.sqrt 2) * (∑ i, ∑ j,
    (Real.sqrt 2*v i)*(Real.sqrt 2*u j)*qMatrix a i j) = _
  have hm (i j : Fin d) : (Real.sqrt 2*v i)*(Real.sqrt 2*u j)*qMatrix a i j =
      2*(v i*u j*qMatrix a i j) := by
    calc
      _ = (Real.sqrt 2)^2*(v i*u j*qMatrix a i j) := by ring
      _ = _ := by rw [hs]
  simp_rw [hm, ← Finset.mul_sum]
  rw [he, hd, hp]
  have hscale : (1 / Real.sqrt 2) * 2 = Real.sqrt 2 := by
    field_simp
    nlinarith [hs]
  rw [← mul_assoc, hscale]

private lemma sum_five_collect {I J A B C : Type*} [Fintype I] [Fintype J]
    [Fintype A] [Fintype B] [Fintype C] (f : I → J → C → B → A → ℝ) :
    (∑ i, ∑ j, ∑ c, ∑ b, ∑ a, f i j c b a) =
      ∑ a, ∑ b, ∑ c, ∑ i, ∑ j, f i j c b a := by
  calc
    _ = ∑ c, ∑ i, ∑ j, ∑ b, ∑ a, f i j c b a := sum_three_rotate _
    _ = ∑ c, ∑ b, ∑ i, ∑ j, ∑ a, f i j c b a := by
      apply Finset.sum_congr rfl
      intro c _
      exact sum_three_rotate _
    _ = ∑ c, ∑ b, ∑ a, ∑ i, ∑ j, f i j c b a := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      exact sum_three_rotate _
    _ = ∑ a, ∑ c, ∑ b, ∑ i, ∑ j, f i j c b a := sum_three_rotate _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm

/-- The actual tensor contraction has the ordered sqrt(2) coordinate
expansion; no symmetry of the trilinear form is required. -/
theorem sourceTensorCorrection_coordinate
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => SymFrob d) ℝ) (w : Fin d → ℝ) :
    sourceTensorCorrection T w = Real.sqrt 2 * ∑ a : Index d, ∑ b : Index d, ∑ c : Index d,
      MvPolynomial.eval w (rawQuadratic (qMatrix b*qMatrix a*qMatrix c)) *
        tri T (qSym d c) (qSym d b) (qSym d a) := by
  unfold sourceTensorCorrection
  have htri (i j : Fin d) := tri_coordinates T (sourceB i w) (sourceB j w) (sourceS i j)
  simp_rw [htri]
  rw [sum_five_collect]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  have hterm (i j : Fin d) :
      (1 / Real.sqrt 2) * (coordinates (sourceB i w) c * coordinates (sourceB j w) b *
        coordinates (sourceS i j) a * tri T (qSym d c) (qSym d b) (qSym d a)) =
      ((1 / Real.sqrt 2) * (coordinates (sourceB i w) c * coordinates (sourceB j w) b *
        coordinates (sourceS i j) a)) * tri T (qSym d c) (qSym d b) (qSym d a) := by ring
  simp_rw [hterm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  rw [source_coefficient]
  ring

#print axioms sourceTensorCorrection_coordinate
end GaussianEllipsoid.PaperSymmetricPullback
