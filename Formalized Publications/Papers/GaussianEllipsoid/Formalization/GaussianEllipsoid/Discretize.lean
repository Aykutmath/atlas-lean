/-
Sphere-net discretization for symmetric operator norms (helper H2r2):
pure linear algebra used by the covariance-concentration step of the
Section 4 discharge. The operator norm of a real symmetric matrix is
controlled by the maximum of `|quadratic A|` over an `eps`-net of the
unit ball.
Mathematical source: standard net argument (paper.tex, Section 4,
Davidson-Szarek replacement).
-/
import GaussianEllipsoid.NormBridges
import GaussianEllipsoid.ExactFit

noncomputable section

namespace GaussianEllipsoid

open scoped Matrix

/-! ### Sphere-net discretization for symmetric operator norm

Pure linear algebra: the operator norm of a real symmetric matrix is
controlled by the maximum of `|quadratic A|` over an `eps`-net of the
unit ball, divided by `1 - 2 * eps - eps ^ 2`.
-/

/-- The Euclidean norm of the zero vector. -/
theorem euclidNorm_zero {d : Nat} : euclidNorm (0 : Vector d) = 0 := by
  unfold euclidNorm
  simp

/-- The Euclidean norm vanishes only at zero. -/
theorem euclidNorm_eq_zero_iff {d : Nat} {z : Vector d} :
    euclidNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hsum : ∑ i, (z i) ^ 2 = 0 := by
      rw [← euclidNorm_sq z, h]
      norm_num
    have hall : ∀ i ∈ (Finset.univ : Finset (Fin d)), (z i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i => (z i) ^ 2) (fun i _ => sq_nonneg (z i))).mp hsum
    funext i
    have hi := hall i (Finset.mem_univ i)
    have hi2 : z i * z i = 0 := by
      rw [← pow_two]
      exact hi
    rcases mul_eq_zero.mp hi2 with h' | h' <;> exact h'
  · intro h
    rw [h]
    exact euclidNorm_zero

/-- The dot product of a vector with itself is its squared Euclidean norm. -/
theorem dotProduct_self_eq_euclidNorm_sq {d : Nat} (w : Vector d) :
    w ⬝ᵥ w = (euclidNorm w) ^ 2 := by
  rw [euclidNorm_sq]
  simp only [dotProduct, pow_two]

/-- Quadratic forms are homogeneous of degree two in the vector argument. -/
theorem quadratic_vec_smul {d : Nat} (A : Square d) (c : ℝ) (z : Vector d) :
    quadratic A (c • z) = c ^ 2 * quadratic A z := by
  unfold quadratic
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  ring

/-- The quadratic form vanishes at zero. -/
theorem quadratic_zero_vec {d : Nat} (A : Square d) : quadratic A 0 = 0 := by
  unfold quadratic
  exact zero_dotProduct _

/-- Symmetry lets the matrix slide across the dot product. -/
theorem dotProduct_mulVec_symm_swap {d : Nat} {A : Square d}
    (hsymm : A.IsSymm) (x y : Vector d) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec]
  have hvec : Matrix.vecMul x A = A *ᵥ x := by
    rw [← Matrix.mulVec_transpose, hsymm]
  rw [hvec, dotProduct_comm]

/-- Polarization identity for a symmetric quadratic form. -/
theorem polarization {d : Nat} {A : Square d} (hsymm : A.IsSymm)
    (x y : Vector d) :
    4 * (x ⬝ᵥ (A *ᵥ y))
      = quadratic A (x + y) - quadratic A (x - y) := by
  have hswap : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) :=
    dotProduct_mulVec_symm_swap hsymm y x
  unfold quadratic
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub]
  rw [hswap]
  ring

/-- Parallelogram law for the Euclidean norm. -/
theorem euclidNorm_parallelogram {d : Nat} (x y : Vector d) :
    (euclidNorm (x + y)) ^ 2 + (euclidNorm (x - y)) ^ 2
      = 2 * (euclidNorm x) ^ 2 + 2 * (euclidNorm y) ^ 2 := by
  simp only [euclidNorm_sq, Pi.add_apply, Pi.sub_apply,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Triangle inequality for the Euclidean norm. -/
theorem euclidNorm_add_le {d : Nat} (x y : Vector d) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  have hcs := dotProduct_abs_le_euclidNorm x y
  have hexpand : (euclidNorm (x + y)) ^ 2
      = (euclidNorm x) ^ 2 + 2 * (x ⬝ᵥ y) + (euclidNorm y) ^ 2 := by
    rw [euclidNorm_sq, euclidNorm_sq, euclidNorm_sq]
    simp only [dotProduct, Pi.add_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsq : (euclidNorm (x + y)) ^ 2
      ≤ (euclidNorm x + euclidNorm y) ^ 2 := by
    have hle : x ⬝ᵥ y ≤ euclidNorm x * euclidNorm y :=
      (le_abs_self _).trans hcs
    have hex : (euclidNorm x + euclidNorm y) ^ 2
        = (euclidNorm x) ^ 2 + 2 * (euclidNorm x * euclidNorm y)
          + (euclidNorm y) ^ 2 := by ring
    rw [hexpand, hex]
    linarith [hle]
  have hnn : 0 ≤ euclidNorm x + euclidNorm y :=
    add_nonneg (euclidNorm_nonneg _) (euclidNorm_nonneg _)
  have habs := abs_le_of_sq_le_sq hsq hnn
  rwa [abs_of_nonneg (euclidNorm_nonneg _)] at habs

/-- The Euclidean norm is invariant under negation. -/
theorem euclidNorm_neg {d : Nat} (x : Vector d) :
    euclidNorm (-x) = euclidNorm x := by
  have h : (-x) = (-1 : ℝ) • x := by
    funext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, euclidNorm_smul]
  norm_num

/-- Triangle inequality for a difference. -/
theorem euclidNorm_sub_le {d : Nat} (x y : Vector d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  rw [sub_eq_add_neg]
  calc euclidNorm (x + -y)
      ≤ euclidNorm x + euclidNorm (-y) := euclidNorm_add_le _ _
    _ = euclidNorm x + euclidNorm y := by rw [euclidNorm_neg]

/-- Sphere-net discretization: the symmetric operator norm is controlled by
the largest quadratic-form magnitude on an `eps`-net of the unit ball. -/
theorem opNorm_le_net_max_quadratic {d N : Nat} {A : Square d}
    (hsymm : A.IsSymm) {v : Fin N → Vector d} {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps1 : 2 * eps + eps ^ 2 < 1)
    (hnet : ∀ u : Vector d, euclidNorm u ≤ 1 →
      ∃ k : Fin N, euclidNorm (u - v k) ≤ eps) :
    ∃ k : Fin N,
      matrixOpNorm A
        ≤ |quadratic A (v k)| / (1 - 2 * eps - eps ^ 2) := by
  by_cases hN : N = 0
  · subst hN
    have h0 : euclidNorm (0 : Vector d) ≤ 1 := by
      rw [euclidNorm_zero]
      exact zero_le_one
    obtain ⟨k, -⟩ := hnet 0 h0
    exact Fin.elim0 k
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hNe : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    set S : Set ℝ :=
      {t : ℝ | ∃ z : Vector d, euclidNorm z ≤ 1 ∧ t = |quadratic A z|}
      with hS
    set Q : ℝ := sSup S with hQ
    have hmem0 : (0 : ℝ) ∈ S := by
      refine ⟨0, ?_, ?_⟩
      · rw [euclidNorm_zero]
        exact zero_le_one
      · rw [quadratic_zero_vec, abs_zero]
    have hne : S.Nonempty := ⟨0, hmem0⟩
    have hbdd : BddAbove S := by
      refine ⟨matrixOpNorm A, ?_⟩
      rintro t ⟨z, hz, rfl⟩
      have h1 := quadratic_abs_le_opNorm_mul_sq A z
      have hz2 : (euclidNorm z) ^ 2 ≤ 1 := by
        nlinarith [hz, euclidNorm_nonneg z]
      calc |quadratic A z|
          ≤ matrixOpNorm A * (euclidNorm z) ^ 2 := h1
        _ ≤ matrixOpNorm A * 1 :=
            mul_le_mul_of_nonneg_left hz2 (matrixOpNorm_nonneg _)
        _ = matrixOpNorm A := mul_one _
    have hQnn : 0 ≤ Q := by
      rw [hQ]
      exact le_csSup hbdd hmem0
    -- Homogeneous bound: every quadratic value is controlled by `Q`.
    have hscaled : ∀ z : Vector d,
        |quadratic A z| ≤ Q * (euclidNorm z) ^ 2 := by
      intro z
      by_cases hz0 : z = 0
      · subst hz0
        rw [quadratic_zero_vec, abs_zero, euclidNorm_zero]
        simp
      · have hpos : 0 < euclidNorm z := by
          have hsum : 0 < ∑ i, (z i) ^ 2 := by
            obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
              by_contra hall
              push Not at hall
              apply hz0
              funext i
              exact hall i
            have hvi : 0 < (z i) ^ 2 := by
              rw [pow_two]
              exact mul_self_pos.mpr hi
            exact Finset.sum_pos' (fun i _ => sq_nonneg _)
              ⟨i, Finset.mem_univ i, hvi⟩
          have heq : euclidNorm z = Real.sqrt (∑ i, (z i) ^ 2) := rfl
          rw [heq]
          exact (Real.sqrt_pos).mpr hsum
        set w : Vector d := (euclidNorm z)⁻¹ • z with hw
        have hw1 : euclidNorm w = 1 := by
          rw [hw, euclidNorm_smul,
            abs_of_nonneg (inv_nonneg.mpr hpos.le),
            inv_mul_cancel₀ hpos.ne']
        have hleQ : |quadratic A w| ≤ Q := by
          rw [hQ]
          apply le_csSup hbdd
          exact ⟨w, hw1.le, rfl⟩
        have hdecomp : z = euclidNorm z • w := by
          rw [hw, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hpos.ne',
            one_smul]
        have hq : quadratic A z
            = (euclidNorm z) ^ 2 * quadratic A w := by
          conv_lhs => rw [hdecomp]
          exact quadratic_vec_smul A (euclidNorm z) w
        have habs2 : |(euclidNorm z) ^ 2| = (euclidNorm z) ^ 2 :=
          abs_of_nonneg (sq_nonneg _)
        calc |quadratic A z|
            = |(euclidNorm z) ^ 2 * quadratic A w| := by rw [hq]
          _ = (euclidNorm z) ^ 2 * |quadratic A w| := by
              rw [abs_mul, habs2]
          _ ≤ (euclidNorm z) ^ 2 * Q :=
              mul_le_mul_of_nonneg_left hleQ (sq_nonneg _)
          _ = Q * (euclidNorm z) ^ 2 := by ring
    -- Step 1a: operator action on the unit ball is bounded by `Q`.
    have hunit : ∀ x : Vector d,
        euclidNorm x ≤ 1 → euclidNorm (A *ᵥ x) ≤ Q := by
      intro x hx
      by_cases hw0 : A *ᵥ x = 0
      · rw [hw0, euclidNorm_zero]
        exact hQnn
      · set w : Vector d := A *ᵥ x with hw
        have hnpos : 0 < euclidNorm w := by
          have hne' : euclidNorm w ≠ 0 := by
            intro hcon
            exact hw0 (euclidNorm_eq_zero_iff.mp hcon)
          exact lt_of_le_of_ne' (euclidNorm_nonneg w) hne'
        set y : Vector d := (euclidNorm w)⁻¹ • w with hy
        have hy1 : euclidNorm y = 1 := by
          rw [hy, euclidNorm_smul,
            abs_of_nonneg (inv_nonneg.mpr hnpos.le),
            inv_mul_cancel₀ hnpos.ne']
        have hnorm_eq : w ⬝ᵥ y = euclidNorm w := by
          rw [hy, dotProduct_smul, smul_eq_mul,
            dotProduct_self_eq_euclidNorm_sq, pow_two,
            inv_mul_cancel_left₀ hnpos.ne']
        have hlink : w ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
          rw [hw, dotProduct_comm (A *ᵥ x) y,
            dotProduct_mulVec_symm_swap hsymm y x]
        have hpol := polarization hsymm x y
        have hq1 := hscaled (x + y)
        have hq2 := hscaled (x - y)
        have hpara := euclidNorm_parallelogram x y
        have hx2 : (euclidNorm x) ^ 2 ≤ 1 := by
          nlinarith [hx, euclidNorm_nonneg x]
        have hle : quadratic A (x + y) - quadratic A (x - y)
            ≤ Q * ((euclidNorm (x + y)) ^ 2
              + (euclidNorm (x - y)) ^ 2) := by
          calc quadratic A (x + y) - quadratic A (x - y)
              ≤ Q * (euclidNorm (x + y)) ^ 2
                  + Q * (euclidNorm (x - y)) ^ 2 := by
                have g1 : quadratic A (x + y)
                    ≤ Q * (euclidNorm (x + y)) ^ 2 :=
                  (le_abs_self _).trans hq1
                have g2 : -(quadratic A (x - y))
                    ≤ Q * (euclidNorm (x - y)) ^ 2 :=
                  (neg_le_abs _).trans hq2
                linarith
            _ = Q * ((euclidNorm (x + y)) ^ 2
                + (euclidNorm (x - y)) ^ 2) := by ring
        have hparaQ : Q * ((euclidNorm (x + y)) ^ 2
              + (euclidNorm (x - y)) ^ 2) ≤ 4 * Q := by
          rw [hpara, hy1]
          calc Q * (2 * (euclidNorm x) ^ 2 + 2 * (1 : ℝ) ^ 2)
              ≤ Q * (2 * 1 + 2 * 1) := by
                apply mul_le_mul_of_nonneg_left _ hQnn
                calc (2 : ℝ) * (euclidNorm x) ^ 2 + 2 * (1 : ℝ) ^ 2
                    ≤ 2 * 1 + 2 * 1 ^ 2 := by
                      apply add_le_add_left _ _
                      exact mul_le_mul_of_nonneg_left hx2 (by norm_num)
                  _ = 2 * 1 + 2 * 1 := by rw [one_pow]
            _ = 4 * Q := by ring
        have h4 : 4 * (x ⬝ᵥ (A *ᵥ y)) ≤ 4 * Q := by
          rw [hpol]
          exact hle.trans hparaQ
        have hmain : x ⬝ᵥ (A *ᵥ y) ≤ Q := by linarith
        calc euclidNorm w = w ⬝ᵥ y := hnorm_eq.symm
          _ = x ⬝ᵥ (A *ᵥ y) := hlink
          _ ≤ Q := hmain
    -- Step 1b/1c: the operator norm is bounded by `Q`.
    have hop_le : matrixOpNorm A ≤ Q := by
      apply matrixOpNorm_le_of_euclid_le hQnn
      intro x
      by_cases hx0 : x = 0
      · subst hx0
        rw [Matrix.mulVec_zero, euclidNorm_zero, mul_zero]
      · have hnpos : 0 < euclidNorm x := by
          have hne' : euclidNorm x ≠ 0 := fun hcon =>
            hx0 (euclidNorm_eq_zero_iff.mp hcon)
          exact lt_of_le_of_ne' (euclidNorm_nonneg x) hne'
        set u : Vector d := (euclidNorm x)⁻¹ • x with hu
        have hu1 : euclidNorm u ≤ 1 := by
          rw [hu, euclidNorm_smul,
            abs_of_nonneg (inv_nonneg.mpr hnpos.le),
            inv_mul_cancel₀ hnpos.ne']
        have hAu := hunit u hu1
        have hxdecomp : x = euclidNorm x • u := by
          rw [hu, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hnpos.ne',
            one_smul]
        have hrewrite : euclidNorm (A *ᵥ x)
            = euclidNorm x * euclidNorm (A *ᵥ u) := by
          conv_lhs => rw [hxdecomp, Matrix.mulVec_smul, euclidNorm_smul,
            abs_of_nonneg hnpos.le]
        rw [hrewrite]
        calc euclidNorm x * euclidNorm (A *ᵥ u)
            ≤ euclidNorm x * Q :=
              mul_le_mul_of_nonneg_left hAu hnpos.le
          _ = Q * euclidNorm x := mul_comm _ _
    -- Step 2 setup: quadratic difference across a net edge.
    have hdiff : ∀ (u vk : Vector d),
        quadratic A u - quadratic A vk
          = (u - vk) ⬝ᵥ (A *ᵥ u) + vk ⬝ᵥ (A *ᵥ (u - vk)) := by
      intro u vk
      have hdecomp : u = vk + (u - vk) := by abel
      conv_lhs => rw [hdecomp]
      unfold quadratic
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
        dotProduct_add, dotProduct_sub]
      ring
    have hper : ∀ u : Vector d, euclidNorm u ≤ 1 →
        ∃ k : Fin N, |quadratic A u| ≤ |quadratic A (v k)|
          + (2 * eps + eps ^ 2) * matrixOpNorm A := by
      intro u hu
      obtain ⟨k, hk⟩ := hnet u hu
      refine ⟨k, ?_⟩
      set e : Vector d := u - v k with he
      have hvk : euclidNorm (v k) ≤ 1 + eps := by
        have htri := euclidNorm_sub_le u e
        have heq : v k = u - e := by
          rw [he]
          exact (sub_sub_cancel u (v k)).symm
        rw [heq]
        calc euclidNorm (u - e)
            ≤ euclidNorm u + euclidNorm e := htri
          _ ≤ 1 + eps := add_le_add hu hk
      have hAu : euclidNorm (A *ᵥ u)
          ≤ matrixOpNorm A * euclidNorm u :=
        matrixOpNorm_mulVec_le A u
      have hAe : euclidNorm (A *ᵥ e)
          ≤ matrixOpNorm A * euclidNorm e :=
        matrixOpNorm_mulVec_le A e
      have hcs1 := dotProduct_abs_le_euclidNorm e (A *ᵥ u)
      have hcs2 := dotProduct_abs_le_euclidNorm (v k) (A *ᵥ e)
      have hde := hdiff u (v k)
      have hbound : |quadratic A u - quadratic A (v k)|
          ≤ (2 * eps + eps ^ 2) * matrixOpNorm A := by
        rw [hde, ← he]
        calc |e ⬝ᵥ (A *ᵥ u) + (v k) ⬝ᵥ (A *ᵥ e)|
              ≤ |e ⬝ᵥ (A *ᵥ u)| + |(v k) ⬝ᵥ (A *ᵥ e)| :=
                abs_add_le _ _
            _ ≤ euclidNorm e * euclidNorm (A *ᵥ u)
                  + euclidNorm (v k) * euclidNorm (A *ᵥ e) :=
                add_le_add hcs1 hcs2
            _ ≤ eps * (matrixOpNorm A * 1)
                  + (1 + eps) * (matrixOpNorm A * eps) := by
                apply add_le_add
                · calc euclidNorm e * euclidNorm (A *ᵥ u)
                        ≤ eps * euclidNorm (A *ᵥ u) :=
                          mul_le_mul_of_nonneg_right hk
                            (euclidNorm_nonneg _)
                      _ ≤ eps * (matrixOpNorm A * 1) := by
                          apply mul_le_mul_of_nonneg_left _ heps0
                          calc euclidNorm (A *ᵥ u)
                              ≤ matrixOpNorm A * euclidNorm u := hAu
                            _ ≤ matrixOpNorm A * 1 :=
                                mul_le_mul_of_nonneg_left hu
                                  (matrixOpNorm_nonneg _)
                · calc euclidNorm (v k) * euclidNorm (A *ᵥ e)
                        ≤ (1 + eps) * euclidNorm (A *ᵥ e) :=
                          mul_le_mul_of_nonneg_right hvk
                            (euclidNorm_nonneg _)
                      _ ≤ (1 + eps) * (matrixOpNorm A * eps) := by
                          apply mul_le_mul_of_nonneg_left _
                            (by linarith : (0 : ℝ) ≤ 1 + eps)
                          calc euclidNorm (A *ᵥ e)
                              ≤ matrixOpNorm A * euclidNorm e := hAe
                            _ ≤ matrixOpNorm A * eps :=
                                mul_le_mul_of_nonneg_left hk
                                  (matrixOpNorm_nonneg _)
            _ = (2 * eps + eps ^ 2) * matrixOpNorm A := by ring
      have htri_abs : |quadratic A u| ≤ |quadratic A (v k)|
          + |quadratic A u - quadratic A (v k)| := by
        have h := abs_sub_abs_le_abs_sub (quadratic A u)
          (quadratic A (v k))
        linarith
      calc |quadratic A u|
          ≤ |quadratic A (v k)|
              + |quadratic A u - quadratic A (v k)| := htri_abs
        _ ≤ |quadratic A (v k)|
            + (2 * eps + eps ^ 2) * matrixOpNorm A :=
            add_le_add_right hbound _
    -- Step 3: maximize over the net and rearrange.
    obtain ⟨k0⟩ := hNe
    obtain ⟨kmax, -, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun k : Fin N => |quadratic A (v k)|)
      ⟨k0, Finset.mem_univ k0⟩
    have hQle : Q ≤ |quadratic A (v kmax)|
        + (2 * eps + eps ^ 2) * matrixOpNorm A := by
      rw [hQ]
      apply csSup_le hne
      rintro t ⟨u, hu, rfl⟩
      obtain ⟨k, hk'⟩ := hper u hu
      calc |quadratic A u|
          ≤ |quadratic A (v k)|
              + (2 * eps + eps ^ 2) * matrixOpNorm A := hk'
        _ ≤ |quadratic A (v kmax)|
            + (2 * eps + eps ^ 2) * matrixOpNorm A :=
            add_le_add_left (hmax k (Finset.mem_univ k)) _
    have hcomb : matrixOpNorm A * (1 - 2 * eps - eps ^ 2)
        ≤ |quadratic A (v kmax)| := by
      linarith [hop_le, hQle]
    have hpos : (0 : ℝ) < 1 - 2 * eps - eps ^ 2 := by
      linarith [heps1]
    refine ⟨kmax, ?_⟩
    rw [le_div_iff₀ hpos]
    exact hcomb

end GaussianEllipsoid
