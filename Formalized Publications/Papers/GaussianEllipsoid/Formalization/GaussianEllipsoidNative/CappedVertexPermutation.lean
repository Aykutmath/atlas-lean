import CappedSimplexRemainder
import RegularizedExpectationSymmetry

noncomputable section
open Finset
namespace GaussianEllipsoid.CappedSimplex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem almost_vertex_perm {a : ℝ} (ha : 0 < a) {v w : ι → ℝ}
    (hv : v ∈ slice a 1) (hw : w ∈ slice a 1)
    (hvc : (interior a v).card ≤ 1) (hwc : (interior a w).card ≤ 1) :
    ∃ e : Equiv.Perm ι, v = w ∘ e := by
  let S := Finset.univ.filter (fun i => v i = a)
  let T := Finset.univ.filter (fun i => w i = a)
  have hvshape := almost_vertex_cap_remainder ha hv hvc
  have hwshape := almost_vertex_cap_remainder ha hw hwc
  obtain ⟨e, he⟩ := exists_perm_mem_iff S T (hvshape.1.trans hwshape.1.symm)
  have hecap (i : ι) : w (e i) = a ↔ v i = a := by simpa [S, T] using he i
  have hzero {f : ι → ℝ} (hf : f ∈ slice a 1) {i : ι}
      (hin : i ∉ interior a f) (hne : f i ≠ a) : f i = 0 := by
    by_contra hn
    exact hin (mem_interior.mpr ⟨lt_of_le_of_ne (hf.1 i).1 (Ne.symm hn),
      lt_of_le_of_ne (hf.1 i).2 hne⟩)
  by_cases hvempty : interior a v = ∅
  · have hvrep : v = fun i => if i ∈ S then a else 0 := by
      funext i
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using (Finset.mem_filter.mp hi).2
      · simp only [if_neg hi]
        exact hzero hv (by simp [hvempty]) (by simpa [S] using hi)
    have hsumv : (S.card : ℝ)*a = 1 := by simpa [hvrep] using hv.2
    have hwrho : 1 - (Nat.floor (1/a):ℝ)*a = 0 := by rw [← hvshape.1]; linarith
    refine ⟨e, ?_⟩
    funext i
    rcases hwshape.2 (e i) with hz | hc | hr
    · have hvi : v i ≠ a := by intro hi; exact ha.ne' (hz ▸ (hecap i).mpr hi).symm
      exact (hzero hv (by simp [hvempty]) hvi).trans hz.symm
    · exact ((hecap i).mp hc).trans hc.symm
    · rw [hwrho] at hr
      have hvi : v i ≠ a := by intro hi; exact ha.ne' (hr ▸ (hecap i).mpr hi).symm
      exact (hzero hv (by simp [hvempty]) hvi).trans hr.symm
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hvempty
    have hj' := mem_interior.mp hj
    have hvj : v j = 1 - (Nat.floor (1/a):ℝ)*a := by
      rcases hvshape.2 j with h | h | h
      · exact False.elim (hj'.1.ne' h)
      · exact False.elim (hj'.2.ne h)
      · exact h
    have hwnonempty : (interior a w).Nonempty := by
      by_contra hh
      have hwe : interior a w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
      have hwrep : w = fun i => if i ∈ T then a else 0 := by
        funext i
        by_cases hi : i ∈ T
        · simpa only [if_pos hi] using (Finset.mem_filter.mp hi).2
        · simp only [if_neg hi]
          exact hzero hw (by simp [hwe]) (by simpa [T] using hi)
      have hsumw : (T.card:ℝ)*a = 1 := by simpa [hwrep] using hw.2
      rw [hwshape.1] at hsumw
      linarith
    obtain ⟨k, hk⟩ := hwnonempty
    have hk' := mem_interior.mp hk
    have hwk : w k = 1 - (Nat.floor (1/a):ℝ)*a := by
      rcases hwshape.2 k with h | h | h
      · exact False.elim (hk'.1.ne' h)
      · exact False.elim (hk'.2.ne h)
      · exact h
    let l := e.symm k
    let σ := Equiv.swap j l
    refine ⟨σ.trans e, ?_⟩
    funext i
    change v i = w (e (σ i))
    by_cases hij : i = j
    · subst i
      simp only [σ, Equiv.swap_apply_left, l, Equiv.apply_symm_apply]
      exact hvj.trans hwk.symm
    by_cases hil : i = l
    · subst i
      simp only [σ, Equiv.swap_apply_right]
      have hvln : v l ≠ a := by
        intro hl
        have hh := (hecap l).mpr hl
        simp only [l, Equiv.apply_symm_apply] at hh
        exact hk'.2.ne hh
      have hvl : v l = 0 := hzero hv (by
        intro hh
        exact hij ((Finset.card_le_one.mp hvc) l hh j hj)) hvln
      have hwejn : w (e j) ≠ a := by intro hh; exact hj'.2.ne ((hecap j).mp hh)
      have hwej : w (e j) = 0 := hzero hw (by
        intro hh
        have h := (Finset.card_le_one.mp hwc) (e j) hh k hk
        have hh : j = l := by simpa [l] using congrArg e.symm h
        exact hij hh.symm) hwejn
      exact hvl.trans hwej.symm
    · have hσi : σ i = i := Equiv.swap_apply_of_ne_of_ne hij hil
      rw [hσi]
      by_cases hvi : v i = a
      · exact hvi.trans ((hecap i).mpr hvi).symm
      have hvin : i ∉ interior a v := by
        intro hh
        exact hij ((Finset.card_le_one.mp hvc) i hh j hj)
      have hwin : e i ∉ interior a w := by
        intro hh
        have h := (Finset.card_le_one.mp hwc) (e i) hh k hk
        exact hil (by simpa [l] using congrArg e.symm h)
      exact (hzero hv hvin hvi).trans (hzero hw hwin (by
        intro hh; exact hvi ((hecap i).mp hh))).symm
end GaussianEllipsoid.CappedSimplex
