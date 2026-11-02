/-
UC7-C5-1 corrected: eigenvalue-weighted elliptic bound.

The as-briefed gap `|(S*E).trace| ≤ hi * E.trace` for `S ∈ box`, `E` PSD is
FALSE without sign control (counterexample d=1, lo=-2, hi=1, S=(-2)•I, E=I:
|Tr| = 2 > 1; see /tmp/u7h_ell/ELLIPTIC.md §3). With the paper's standing
hypotheses `0 ≤ lo ≤ hi`, `S` is PSD and the bound holds. The single missing
ingredient `psd_trace_mul_nonneg` is proved here by generalizing
`trace_box_mul_expand` to take `S.IsHermitian` directly (its proof uses only
the Hermitian structure, never the box).
-/
import GaussianEllipsoid.HuberDischarge

noncomputable section

namespace GaussianEllipsoid

/-- Spectral expansion of `Tr(SE)` for Hermitian `S`: generalization of
`trace_box_mul_expand` (identical proof, `hH` in place of the box). -/
theorem trace_hermitian_mul_expand {d : Nat} {S E : Square d}
    (hH : S.IsHermitian) :
    (S * E).trace = ∑ i, hH.eigenvalues i *
      quadratic E ⇑(hH.eigenvectorBasis i) := by
  have hspec := hH.spectral_theorem
  set U : Square d := ↑hH.eigenvectorUnitary with hUdef
  have hcol : ∀ i l : Fin d, U l i
      = (⇑(hH.eigenvectorBasis i) : Vector d) l :=
    fun i l => hH.eigenvectorUnitary_apply l i
  have hstar : ∀ a b : Fin d, (star U) a b = U b a := by
    intro a b
    rw [Matrix.star_apply]
    exact star_trivial _
  have hstep1 : (S * E).trace
      = (((star U * E) * U) * Matrix.diagonal
        (RCLike.ofReal ∘ hH.eigenvalues)).trace := by
    conv_lhs => rw [hspec, Unitary.conjStarAlgAut_apply]
    simp only [mul_assoc, ← hUdef]
    rw [Matrix.trace_mul_cycle']
    simp only [mul_assoc]
  rw [hstep1, trace_mul_diagonal_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  have hB : (((star U * E) * U)) i i
      = quadratic E ⇑(hH.eigenvectorBasis i) := by
    simp only [Matrix.mul_apply, hstar, hcol, Finset.sum_mul]
    rw [Finset.sum_comm]
    unfold quadratic
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hB]
  have hof : RCLike.ofReal (hH.eigenvalues i) = hH.eigenvalues i := by simp
  rw [hof]
  ring

/-- Trace of a PSD product is nonnegative (the missing lemma; absent from
both repo and Mathlib). -/
theorem psd_trace_mul_nonneg {d : Nat} {A B : Square d}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have hH := hA.isHermitian
  rw [trace_hermitian_mul_expand hH]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hH.posSemidef_iff_eigenvalues_nonneg.mp hA i)
    (posSemidef_quadratic_nonneg hB _)

/-- C5-1 corrected: eigenvalue-weighted elliptic bound under the paper's
standing hypotheses `0 ≤ lo ≤ hi`. -/
theorem ellipticA_weighted_corrected {d : Nat} {lo hi : Real}
    {S E : Square d} (hS : S ∈ spectralBox d lo hi)
    (hlo : 0 ≤ lo) (hle : lo ≤ hi) (hE : E.PosSemidef) :
    |(S * E).trace| ≤ hi * E.trace := by
  have hSpsd : S.PosSemidef := posSemidef_of_mem_box hlo hS
  have hnn : 0 ≤ (S * E).trace := psd_trace_mul_nonneg hSpsd hE
  have hgap : 0 ≤ ((hi • (1 : Square d) - S) * E).trace :=
    psd_trace_mul_nonneg hS.2 hE
  have hexpand : ((hi • (1 : Square d) - S) * E).trace
      = hi * E.trace - (S * E).trace := by
    rw [sub_mul, Matrix.trace_sub, smul_mul_assoc, Matrix.trace_smul,
      Matrix.one_mul, smul_eq_mul]
  rw [hexpand] at hgap
  have hhi : 0 ≤ hi := le_trans hlo hle
  have hEtr : 0 ≤ E.trace := hE.trace_nonneg
  have hup : (S * E).trace ≤ hi * E.trace := by linarith
  rw [abs_le]
  constructor <;> linarith [mul_nonneg hhi hEtr]

end GaussianEllipsoid
