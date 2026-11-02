import BMGordonGeometry

noncomputable section
open scoped InnerProductSpace
open GaussianEllipsoid BMGeometry BMSaddle BMGordon
namespace UCEscape

lemma csInf_range_add {K : Type*} [Nonempty K] (f : K → ℝ)
    (hf : BddBelow (Set.range f)) (c : ℝ) :
    sInf (Set.range (fun k => f k+c)) = sInf (Set.range f)+c := by
  obtain ⟨b,hb⟩ := hf
  have hs : BddBelow (Set.range (fun k => f k+c)) := by
    refine ⟨b+c, ?_⟩
    rintro z ⟨k,rfl⟩
    have h := hb ⟨k,rfl⟩
    linarith
  apply le_antisymm
  · have h : sInf (Set.range (fun k => f k+c))-c ≤ sInf (Set.range f) := by
      apply le_csInf (Set.range_nonempty _)
      rintro z ⟨k,rfl⟩
      have h := csInf_le hs (show f k+c ∈ Set.range (fun k => f k+c) from ⟨k,rfl⟩)
      linarith
    linarith
  · apply le_csInf (Set.range_nonempty _)
    rintro z ⟨k,rfl⟩
    have h := csInf_le ⟨b,hb⟩ ⟨k,rfl⟩
    linarith

lemma inner_unitSphere_maximum {n : ℕ} (hn : 0 < n) (v : Euclid n) :
    ∃ u : UnitSample n, ⟪(u : Euclid n),v⟫_ℝ = ‖v‖ ∧
      ∀ w : UnitSample n, ⟪(w : Euclid n),v⟫_ℝ ≤ ‖v‖ := by
  have hb (w : UnitSample n) : ⟪(w : Euclid n),v⟫_ℝ ≤ ‖v‖ := by
    simpa only [unitSample_norm, one_mul] using real_inner_le_norm (w : Euclid n) v
  by_cases hv : v = 0
  · obtain ⟨u⟩ := unitSample_nonempty hn
    exact ⟨u, by simp [hv], hb⟩
  · have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : Euclid n := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
    refine ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩, ?_, hb⟩
    change ⟪‖v‖⁻¹ • v,v⟫_ℝ = ‖v‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

lemma inner_unitSphere_sup_add {n : ℕ} (hn : 0 < n) (v : Euclid n) (c : ℝ) :
    sSup ((fun u : UnitSample n => ⟪(u : Euclid n),v⟫_ℝ+c) '' Set.univ) = ‖v‖+c := by
  obtain ⟨u,hu,hb⟩ := inner_unitSphere_maximum hn v
  apply IsGreatest.csSup_eq
  refine ⟨⟨u, Set.mem_univ _, ?_⟩, ?_⟩
  · exact congrArg (fun t => t+c) hu
  · rintro z ⟨w,_,rfl⟩
    have h := hb w
    linarith

#print axioms inner_unitSphere_sup_add
end UCEscape
