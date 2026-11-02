/-
Deterministic net-to-continuum bridges for `UniformConicBound`: generic
sup-contraction and inf net-min patterns plus their instantiation for the
conic margin functional `conicInf`.

All results are deterministic (no measure, no Gaussian facts) and
conditional on explicit finite-net cover premises. Net
existence/cardinality (volume-comparison counts) are NOT proved here.
Mathematical source: paper.tex, lines 3757-3766, 4191-4210, 4608-4666.
-/
import GaussianEllipsoid.AboveObjects

noncomputable section

namespace GaussianEllipsoid

/-! ### Generic sup contraction (paper ll.3757-3766 pattern) -/

/-- Self-bounding sup: if every element of `s` is at most `M + r * sSup s`
with `r < 1`, then `sSup s ≤ M / (1 - r)`. This is the deterministic core
of the `Λ_p` net step. -/
theorem sSup_le_of_forall_le_add_mul_sSup {s : Set ℝ} {M r : ℝ}
    (hne : s.Nonempty) (hr : r < 1)
    (h : ∀ t ∈ s, t ≤ M + r * sSup s) :
    sSup s ≤ M / (1 - r) := by
  have hQ : sSup s ≤ M + r * sSup s := csSup_le hne h
  have hpos : (0 : ℝ) < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  linarith [hQ]

/-! ### Generic inf net-min bridge (paper ll.4191-4210 pattern) -/

/-- Continuum inf from a finite net: if every `t ∈ s` lies above some net
value minus `e`, then some net value minus `e` lies below `sInf s`. -/
theorem sInf_ge_net_min_sub {s : Set ℝ} {N : ℕ} {f : Fin N → ℝ} {e : ℝ}
    (hne : s.Nonempty) (hN : 0 < N)
    (h : ∀ t ∈ s, ∃ k : Fin N, f k - e ≤ t) :
    ∃ k : Fin N, f k - e ≤ sInf s := by
  obtain ⟨k0⟩ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨kmin, -, hmin⟩ := Finset.exists_min_image Finset.univ f
    ⟨k0, Finset.mem_univ k0⟩
  refine ⟨kmin, le_csInf hne ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := h t ht
  have hle : f kmin ≤ f k := hmin k (Finset.mem_univ k)
  linarith

/-- Pointwise Lipschitz error as a one-sided bound. -/
theorem sub_le_of_abs_sub_le {a b e : ℝ} (h : |a - b| ≤ e) :
    b - e ≤ a := by
  have hneg : -(a - b) ≤ |a - b| := neg_le_abs _
  linarith [h, hneg]

/-! ### Conic-margin instantiation (`conicInf`, AboveObjects.lean) -/

/-- The conic margin value at one matrix: `(1/n) ‖Π₀ Q(S)‖₁`. -/
def conicMargin {d n : ℕ} (x : Sample d n) (S : Square d) : ℝ :=
  (1 / (n : ℝ)) * l1Size (center (measurementQ x S))

/-- Net-to-continuum lower bound for `conicInf`: given PSD Frobenius-unit
centers whose margin values `e`-cover every continuum value from below,
some center value minus `e` bounds `conicInf` below. The cover premise is
exactly what a Lipschitz estimate plus a Frobenius `r`-net supplies. -/
theorem conicInf_ge_net_min_sub {d n N : ℕ} (hd : 0 < d)
    (x : Sample d n) (centers : Fin N → Square d) (hN : 0 < N) {e : ℝ}
    (hcover : ∀ S : Square d, S.PosSemidef → frobeniusNorm S = 1 →
      ∃ k : Fin N, conicMargin x (centers k) - e ≤ conicMargin x S) :
    ∃ k : Fin N, conicMargin x (centers k) - e ≤ conicInf d n x := by
  have hne : {t : ℝ | ∃ S : Square d, S.PosSemidef ∧ frobeniusNorm S = 1 ∧
      t = conicMargin x S}.Nonempty := by
    set i₀ : Fin d := ⟨0, hd⟩ with hi₀
    set e0 : Vector d := Pi.single i₀ 1 with he0
    have hsum : ∑ i, (e0 i) ^ 2 = 1 := by
      have hfun : (fun i => (e0 i) ^ 2) = Pi.single i₀ 1 := by
        funext i
        by_cases h : i = i₀
        · subst h
          simp [he0]
        · simp [he0, h]
      rw [hfun]
      simp
    have hpsd : (Matrix.vecMulVec e0 e0).PosSemidef := by
      have h := Matrix.posSemidef_vecMulVec_self_star e0
      have hstar : star e0 = e0 := by
        funext i
        simp [he0]
      rw [hstar] at h
      exact h
    have hF : frobeniusNorm (Matrix.vecMulVec e0 e0) = 1 := by
      have hsq : (frobeniusNorm (Matrix.vecMulVec e0 e0)) ^ 2 = 1 := by
        rw [frobeniusNorm_vecMulVec_sq, hsum, mul_one]
      have hnn := frobeniusNorm_nonneg (Matrix.vecMulVec e0 e0)
      conv_lhs => rw [← Real.sqrt_sq hnn]
      rw [hsq, Real.sqrt_one]
    exact ⟨conicMargin x (Matrix.vecMulVec e0 e0),
      Matrix.vecMulVec e0 e0, hpsd, hF, rfl⟩
  have hset : ∀ t ∈ {t : ℝ | ∃ S : Square d, S.PosSemidef ∧
      frobeniusNorm S = 1 ∧ t = conicMargin x S},
      ∃ k : Fin N, conicMargin x (centers k) - e ≤ t := by
    rintro t ⟨S, hS, hF, rfl⟩
    exact hcover S hS hF
  obtain ⟨k, hk⟩ := sInf_ge_net_min_sub hne hN hset
  refine ⟨k, ?_⟩
  have hunfold : conicInf d n x
      = sInf {t : ℝ | ∃ S : Square d, S.PosSemidef ∧ frobeniusNorm S = 1 ∧
        t = conicMargin x S} := by
    unfold conicInf conicMargin
    rfl
  rw [hunfold]
  exact hk

/-- Absolute-cover form matching the paper's `L₁(A*r + s)` step. -/
theorem conicInf_ge_net_min_of_abs_cover {d n N : ℕ} (hd : 0 < d)
    (x : Sample d n) (centers : Fin N → Square d) (hN : 0 < N) {e : ℝ}
    (hcover : ∀ S : Square d, S.PosSemidef → frobeniusNorm S = 1 →
      ∃ k : Fin N, |conicMargin x S - conicMargin x (centers k)| ≤ e) :
    ∃ k : Fin N, conicMargin x (centers k) - e ≤ conicInf d n x := by
  apply conicInf_ge_net_min_sub hd x centers hN
  intro S hS hF
  obtain ⟨k, hk⟩ := hcover S hS hF
  exact ⟨k, sub_le_of_abs_sub_le hk⟩

end GaussianEllipsoid
