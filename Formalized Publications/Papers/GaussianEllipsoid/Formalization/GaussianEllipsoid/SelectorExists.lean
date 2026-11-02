/-
Discharge of the Huber selector existence premise (paper Section 4):
the spectral box is nonempty and compact, the Huber-plus-ridge
objective is continuous, so a minimizer exists by Weierstrass.
Mathematical source: paper.tex, Section 4.
-/
import GaussianEllipsoid.Huber
import GaussianEllipsoid.BelowObjects

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace GaussianEllipsoid

/-! ### Continuity of the Huber loss -/

/-- The Huber loss equals a branch-free min/max expression. -/
theorem huber_eq_min_max (t : ℝ) :
    huber t = (min |t| 1) ^ 2 / 2 + max (|t| - 1) 0 := by
  unfold huber
  by_cases h : |t| ≤ 1
  · rw [ite_eq_left h, min_eq_left h, sq_abs,
      max_eq_right (by linarith : |t| - 1 ≤ 0)]
    ring
  · have h1 : 1 ≤ |t| := le_of_not_ge h
    rw [ite_eq_right h, min_eq_right h1,
      max_eq_left (by linarith : 0 ≤ |t| - 1)]
    ring

/-- The Huber loss is continuous. -/
theorem huber_continuous : Continuous huber := by
  have habs : Continuous fun t : ℝ => |t| := by
    simp only [← Real.norm_eq_abs]
    exact continuous_norm
  have heq : huber = fun t : ℝ => (min |t| 1) ^ 2 / 2 + max (|t| - 1) 0 :=
    funext huber_eq_min_max
  rw [heq]
  simp only [pow_two]
  apply Continuous.add
  · apply Continuous.div_const
    exact (habs.min continuous_const).mul (habs.min continuous_const)
  · exact (habs.sub continuous_const).max continuous_const

/-! ### The spectral box is nonempty -/

/-- The spectral box always contains the scaled identity. -/
theorem spectralBox_nonempty {d : Nat} {lo hi : ℝ} (hle : lo ≤ hi) :
    (spectralBox d lo hi).Nonempty := by
  refine ⟨lo • (1 : Square d), ?_, ?_⟩
  · show ((lo • (1 : Square d)) - lo • (1 : Square d)).PosSemidef
    rw [sub_self]
    exact Matrix.PosSemidef.zero
  · show ((hi • (1 : Square d)) - lo • (1 : Square d)).PosSemidef
    rw [← sub_smul]
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
      (sub_nonneg.mpr hle)

/-! ### The spectral box is closed -/

/-- Matrix entries depend continuously on the matrix. -/
theorem entry_continuous {d : Nat} (i j : Fin d) :
    Continuous fun M : Square d => M i j :=
  (continuous_apply j).comp (continuous_apply i)

/-- Symmetric matrices form a closed set. -/
theorem isClosed_setOf_isSymm (d : Nat) :
    IsClosed {M : Square d | M.IsSymm} := by
  have hrewrite : {M : Square d | M.IsSymm}
      = ⋂ i, ⋂ j, {M : Square d | M i j = M j i} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [Matrix.IsSymm.ext_iff]
    constructor
    · intro h i j
      exact (h i j).symm
    · intro h i j
      exact h j i
  rw [hrewrite]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (entry_continuous i j) (entry_continuous j i)

/-- Each quadratic-form slice is a closed condition on the matrix. -/
theorem isClosed_quadratic_nonneg (d : Nat) (x : Fin d → ℝ) :
    IsClosed {M : Square d | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
  have heq : {M : Square d | 0 ≤ star x ⬝ᵥ (M *ᵥ x)}
      = (fun M : Square d => star x ⬝ᵥ (M *ᵥ x)) ⁻¹' (Set.Ici 0) :=
    rfl
  rw [heq]
  have hfun : (fun M : Square d => star x ⬝ᵥ (M *ᵥ x))
      = fun M => ∑ i, (star x) i * ∑ j, M i j * x j :=
    rfl
  have hcont : Continuous (fun M : Square d => star x ⬝ᵥ (M *ᵥ x)) := by
    rw [hfun]
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_finsetSum _ fun j _ =>
        (entry_continuous i j).mul continuous_const)
  exact isClosed_Ici.preimage hcont

/-- The PSD cone is closed. -/
theorem isClosed_setOf_posSemidef (d : Nat) :
    IsClosed {M : Square d | M.PosSemidef} := by
  have hrewrite : {M : Square d | M.PosSemidef}
      = {M | M.IsSymm}
        ∩ ⋂ (x : Fin d → ℝ), {M : Square d | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.isHermitian_iff_isSymm]
  rw [hrewrite]
  exact (isClosed_setOf_isSymm d).inter
    (isClosed_iInter fun x => isClosed_quadratic_nonneg d x)

/-- The spectral box is closed. -/
theorem isClosed_spectralBox (d : Nat) (lo hi : ℝ) :
    IsClosed (spectralBox d lo hi) := by
  have hrewrite : spectralBox d lo hi
      = (fun S : Square d => S - lo • 1) ⁻¹' {M | M.PosSemidef}
        ∩ (fun S : Square d => hi • 1 - S) ⁻¹' {M | M.PosSemidef} := by
    ext S
    simp only [spectralBox, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage]
  rw [hrewrite]
  apply IsClosed.inter
  · exact (isClosed_setOf_posSemidef d).preimage
      (continuous_id.sub continuous_const)
  · exact (isClosed_setOf_posSemidef d).preimage
      (continuous_const.sub continuous_id)

/-! ### Entry bounds on the spectral box -/

/-- Pointwise entry equations for the box shifts. These hold by `rfl`
(defeq through the pi instances); `Pi.sub_apply`/`Pi.smul_apply` cannot
fire through the semireducible `Matrix` definition, so the rewrites
below use these exact-shape bridges. -/
theorem box_entry_sub_lo {d : Nat} (S : Square d) (lo : ℝ) (p q : Fin d) :
    (S - lo • (1 : Square d)) p q
      = S p q - lo • ((1 : Square d) p q) := rfl

theorem box_entry_sub_hi {d : Nat} (S : Square d) (hi : ℝ) (p q : Fin d) :
    (hi • (1 : Square d) - S) p q
      = hi • ((1 : Square d) p q) - S p q := rfl

/-- Diagonal entries lie in the spectral interval. -/
theorem spectralBox_diag {d : Nat} {lo hi : ℝ} {S : Square d} {i : Fin d}
    (hS : S ∈ spectralBox d lo hi) : lo ≤ S i i ∧ S i i ≤ hi := by
  obtain ⟨h1, h2⟩ := hS
  have d1 := Matrix.PosSemidef.diag_nonneg h1 (i := i)
  have d2 := Matrix.PosSemidef.diag_nonneg h2 (i := i)
  rw [box_entry_sub_lo S lo i i] at d1
  rw [box_entry_sub_hi S hi i i] at d2
  simp only [Matrix.one_apply_eq, smul_eq_mul, mul_one] at d1 d2
  constructor <;> linarith

/-- Box elements are symmetric off the diagonal. -/
theorem spectralBox_symm {d : Nat} {lo hi : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (p q : Fin d) (hpq : p ≠ q) :
    S p q = S q p := by
  obtain ⟨h1, -⟩ := hS
  have hsymm : (S - lo • (1 : Square d)).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp h1.isHermitian
  have h := (Matrix.IsSymm.ext_iff.mp hsymm) p q
  rw [box_entry_sub_lo S lo q p, box_entry_sub_lo S lo p q] at h
  simp only [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (Ne.symm hpq),
    smul_eq_mul, mul_zero, sub_zero] at h
  exact h.symm

/-- Off-diagonal entries are bounded by polarization. -/
theorem spectralBox_offdiag {d : Nat} {lo hi : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) {i j : Fin d} (hij : i ≠ j) :
    |S i j| ≤ |lo| + |hi| := by
  have h1 := hS.1
  have hq := Matrix.PosSemidef.dotProduct_mulVec_nonneg h1
  have hstar : ∀ a : Fin d,
      star (Pi.single a (1 : ℝ) : Fin d → ℝ) = Pi.single a 1 := by
    intro a
    funext k
    simp [Pi.star_apply, star_trivial]
  have hmulsub : ∀ A : Square d, ∀ u v : Fin d → ℝ,
      A *ᵥ (u - v) = A *ᵥ u - A *ᵥ v := by
    intro A u v
    simp only [← Matrix.mulVecLin_apply, map_sub]
  have e1 := hq (Pi.single i 1 + Pi.single j 1)
  have e2 := hq (Pi.single i 1 - Pi.single j 1)
  simp only [star_add, hstar, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct, single_dotProduct,
    Matrix.mulVec_single_one, Matrix.col_apply, one_mul] at e1
  simp only [star_sub, hstar, hmulsub, dotProduct_sub,
    sub_dotProduct, single_dotProduct,
    Matrix.mulVec_single_one, Matrix.col_apply, one_mul] at e2
  rw [box_entry_sub_lo S lo i i, box_entry_sub_lo S lo j i,
    box_entry_sub_lo S lo i j, box_entry_sub_lo S lo j j] at e1
  rw [box_entry_sub_lo S lo i i, box_entry_sub_lo S lo j i,
    box_entry_sub_lo S lo i j, box_entry_sub_lo S lo j j] at e2
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne hij,
    Matrix.one_apply_ne (Ne.symm hij), smul_eq_mul, mul_one, mul_zero,
    sub_zero] at e1 e2
  have hji : S j i = S i j := spectralBox_symm hS j i (Ne.symm hij)
  rw [hji] at e1 e2
  obtain ⟨hloi, hhii⟩ := spectralBox_diag (i := i) hS
  obtain ⟨hloj, hhhj⟩ := spectralBox_diag (i := j) hS
  rw [abs_le]
  constructor
  · linarith [e1, e2, hloi, hhii, hloj, hhhj, le_abs_self hi,
      neg_le_abs lo]
  · linarith [e1, e2, hloi, hhii, hloj, hhhj, le_abs_self hi,
      neg_le_abs lo]

/-- Every entry is bounded by `|lo| + |hi|`. -/
theorem spectralBox_entry_bound {d : Nat} {lo hi : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (i j : Fin d) :
    |S i j| ≤ |lo| + |hi| := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨hlo, hhi⟩ := spectralBox_diag (i := i) hS
    rw [abs_le]
    constructor
    · linarith [hlo, neg_le_abs lo, abs_nonneg hi]
    · linarith [hhi, le_abs_self hi, abs_nonneg lo]
  · exact spectralBox_offdiag hS hij

/-! ### The box is compact; the objective is continuous -/

/-- The spectral box is compact: closed plus entrywise bounded. -/
theorem isCompact_spectralBox (d : Nat) (lo hi : ℝ) :
    IsCompact (spectralBox d lo hi) := by
  have hsub : spectralBox d lo hi
      ⊆ Set.pi Set.univ (fun _ : Fin d => Set.pi Set.univ
        (fun _ : Fin d => Set.Icc (-(|lo| + |hi|)) (|lo| + |hi|))) := by
    intro S hS i _ j _
    have hb := spectralBox_entry_bound hS i j
    rw [abs_le] at hb
    exact Set.mem_Icc.mpr hb
  have hcompact : IsCompact (Set.pi Set.univ (fun _ : Fin d =>
      Set.pi Set.univ
        (fun _ : Fin d => Set.Icc (-(|lo| + |hi|)) (|lo| + |hi|)))) :=
    isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_Icc
  exact hcompact.of_isClosed_subset (isClosed_spectralBox d lo hi) hsub

/-- The quadratic measurement is continuous in the matrix. -/
theorem quadratic_continuous {d : Nat} (v : Vector d) :
    Continuous fun S : Square d => quadratic S v := by
  have hexp : (fun S : Square d => quadratic S v)
      = fun S => ∑ k, v k * ∑ l, S k l * v l := by
    funext S
    simp [quadratic, dotProduct, Matrix.mulVec]
  rw [hexp]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_finsetSum _ fun l _ =>
      (entry_continuous k l).mul continuous_const)

/-- Each residual coordinate is continuous in the matrix. -/
theorem residual_continuous {d n : Nat} (x : Sample d n) (i : Fin n) :
    Continuous fun S : Square d => residual x S i := by
  have heq : (fun S : Square d => residual x S i)
      = fun S => (quadratic S (x i) - (d : ℝ)) / Real.sqrt (d : ℝ) := by
    funext S
    rfl
  rw [heq]
  exact ((quadratic_continuous (x i)).sub continuous_const).div_const _

/-- The Huber-plus-ridge objective is continuous in the matrix. -/
theorem huberObjective_continuous {d n : Nat} (x : Sample d n) :
    Continuous fun S : Square d => huberObjective x S := by
  have huber_part : Continuous
      fun S : Square d => empiricalHuber (residual x S) := by
    have heq : (fun S : Square d => empiricalHuber (residual x S))
        = fun S => (∑ j, huber (residual x S j))
          / (Fintype.card (Fin n) : ℝ) := by
      funext S
      simp [empiricalHuber, empiricalAverage]
    rw [heq]
    apply Continuous.div_const
    exact continuous_finsetSum _ fun j _ =>
      huber_continuous.comp (residual_continuous x j)
  have ridge_part : Continuous fun S : Square d => ridgePenalty d S := by
    have heq : (fun S : Square d => ridgePenalty d S)
        = fun S => ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ)) * (‖S - 1‖) ^ 2 := by
      funext S
      simp [ridgePenalty, frobeniusNorm]
    rw [heq]
    simp only [pow_two]
    exact continuous_const.mul
      ((continuous_norm.comp (continuous_id.sub continuous_const)).mul
        (continuous_norm.comp (continuous_id.sub continuous_const)))
  exact huber_part.add ridge_part

/-! ### Selector existence -/

/-- The Huber selector exists: Weierstrass on the compact spectral box.
Discharges `HuberMinimizerExists` (paper Section 4). -/
theorem huberMinimizerExists_theorem : HuberMinimizerExists := by
  intro d n lo hi _ hle x
  have hcompact := isCompact_spectralBox d lo hi
  have hne := spectralBox_nonempty (d := d) hle
  have hcont : ContinuousOn (fun S => huberObjective x S)
      (spectralBox d lo hi) :=
    (huberObjective_continuous x).continuousOn
  obtain ⟨S, hSmem, hSmin⟩ := hcompact.exists_isMinOn hne hcont
  exact ⟨S, hSmem, isMinOn_iff.mp hSmin⟩

end GaussianEllipsoid
