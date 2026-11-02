import VolumetricNets
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section
open Module
open scoped BigOperators
namespace GaussianEllipsoid.PaperNuisanceNet

def toL1 (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] PiLp 1 (fun _ : Fin n => ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
    (WithLp.linearEquiv 1 ℝ (Fin n → ℝ)).symm

@[simp] theorem toL1_apply (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    toL1 n v i = v i := rfl
@[simp] theorem toL1_symm_apply (n : ℕ) (v : PiLp 1 (fun _ : Fin n => ℝ)) (i : Fin n) :
    (toL1 n).symm v i = v i := rfl

theorem norm_toL1 (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖toL1 n v‖ = ∑ i, |v i| := by
  rw [PiLp.norm_eq_of_L1]
  simp only [toL1_apply, Real.norm_eq_abs]

/-- The paper's intrinsic l1 nuisance cover. No fixed-rank assumption and no
extra log n factor: centers remain in L intersect the original l1 ball. -/
theorem exists_intrinsic_l1_net (n : ℕ) (hn : 0 < n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (B s : ℝ) (hB : 0 ≤ B) (hs : 0 < s) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ v ∈ N, v ∈ L ∧ ∑ i, |v i| ≤ B*n) ∧
      (N.card:ℝ) ≤ (1+2*B/s)^(finrank ℝ L) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), v ∈ L → ∑ i, |v i| ≤ B*n →
        ∃ w ∈ N, ∑ i, |v i-w i| < s*n := by
  classical
  let L1 := L.map (toL1 n).toLinearMap
  let back : L1 → EuclideanSpace ℝ (Fin n) := fun v => (toL1 n).symm v.val
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨N,hN,hcard,hnet,hsep⟩ := exists_internal_net
    {v : L1 | ‖v‖ ≤ B*n} (R := B*n) (ε := s*n)
    (by positivity) (by positivity) (fun v hv => hv)
  refine ⟨N.image back, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨?_, ?_⟩
    · obtain ⟨u,hu,heq⟩ := w.property
      have he : back w = u := by
        dsimp [back]
        rw [← heq]
        exact (toL1 n).symm_apply_apply u
      rw [he]
      exact hu
    · have hh := hN w hw
      change ‖w.val‖ ≤ B*n at hh
      rw [PiLp.norm_eq_of_L1] at hh
      simpa only [back, toL1_symm_apply, Real.norm_eq_abs] using hh
  · have hd : finrank ℝ L1 = finrank ℝ L := (toL1 n).finrank_map_eq L
    have hc : ((N.image back).card:ℝ) ≤ N.card := by exact_mod_cast Finset.card_image_le
    apply hc.trans
    apply hcard.trans_eq
    rw [hd]
    congr 2
    field_simp
  · intro v hv hvB
    let u : L1 := ⟨toL1 n v, ⟨v,hv,rfl⟩⟩
    have hu : ‖u‖ ≤ B*n := by
      change ‖toL1 n v‖ ≤ B*n
      rw [norm_toL1]
      exact hvB
    obtain ⟨w,hw,hdist⟩ := hnet u hu
    refine ⟨back w, Finset.mem_image.mpr ⟨w,hw,rfl⟩, ?_⟩
    rw [dist_eq_norm] at hdist
    change ‖u.val-w.val‖ < s*n at hdist
    rw [PiLp.norm_eq_of_L1] at hdist
    simpa only [PiLp.sub_apply, u, toL1_apply, Real.norm_eq_abs,
      back, toL1_symm_apply] using hdist

#print axioms exists_intrinsic_l1_net
end GaussianEllipsoid.PaperNuisanceNet
