import PaperHuberGoodEvent
import PaperHuberLogCalibration

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianEllipsoid

/-- Sharp paper infinity rate, in a stronger fixed-constant high-probability
form. The selector is the same one throughout; no replacement or extra premise. -/
theorem paper_huber_centered_linf
    (n : ℕ → ℕ) (α : ℝ) (hn : ∀ d, 0 < n d)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α)) (hα : 0 < α)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hBM : BMminRisk n lo hi)
    (Sstar : ∀ d, Sample d (n d) → Square d)
    (hStar : ∀ d x, IsHuberMinimizer lo hi x (Sstar d x)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun d => (gaussianSampleLaw d (n d)).real
      {x | C*Real.sqrt (Real.log (d:ℝ)) < ‖center (residual x (Sstar d x))‖})
      atTop (𝓝 0) := by
  obtain ⟨c,hc,hHW⟩ := hansonWrightChaos_theorem lo hi hlo hle
  obtain ⟨K,hK,Good,hGoodLim,hShift⟩ := paper_huber_good_shift n α hn hconv hα lo hi hlo hle hBM
  have hSel : ∀ d : ℕ, ∀ j : Fin (n d), ∃ Sdel : Sample d (n d) → Square d,
      Measurable Sdel ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x)) ∧
      ∀ x y : Sample d (n d), (∀ i, i ≠ j → x i = y i) → Sdel x = Sdel y :=
    fun d j => deletedSelectorMeasurable_theorem d (n d) lo hi hlo hle j
  choose Sdel hSdel using hSel
  have hHWraw (d : ℕ) (j : Fin (n d)) (t : ℝ) (ht : 0 ≤ t) :
      (gaussianSampleLaw d (n d)).real {x | t < |chaosZ (Sdel d j) j x|} ≤
        2*Real.exp (-c*min (t^2) (t*Real.sqrt (d:ℝ))) := by
    exact hHW d (n d) j (Sdel d j) (hSdel d j).1
      (fun x => ((hSdel d j).2.1 x).1) (hSdel d j).2.2 t ht
  let C := 4*Real.sqrt (4/c)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have htail := paper_log_union_tendsto n α c hc hconv
  have htotal := htail.add hGoodLim
  rw [zero_add] at htotal
  have hidx := GGlue.eventually_good_index hα hn hconv
  have hlevel := paperLogLevel_eventually c K hc
  have he := (fin_huberInv_tendsto ((|lo|+|hi|+1)^2)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ htotal
  filter_upwards [hidx,hlevel,hShift,he] with d hd hlev hshift he1
  let t := paperLogLevel c d
  have ht : 0 ≤ t := by dsimp [t,paperLogLevel]; positivity
  have hthresh : C*Real.sqrt (Real.log (d:ℝ)) = 4*t := by dsimp [C,t,paperLogLevel]; ring
  let E : Set (Sample d (n d)) := {x | C*Real.sqrt (Real.log (d:ℝ)) < ‖center (residual x (Sstar d x))‖}
  let F : Set (Sample d (n d)) := ⋃ j : Fin (n d), {x | t+K < |residual x (Sdel d j x) j|}
  have hsub : E ∩ Good d ⊆ F ∩ Good d := by
    intro x hx
    refine ⟨?_,hx.2⟩
    have h0 : 4*t < ‖center (residual x (Sstar d x))‖ := by
      simpa only [E,Set.mem_ofPred_eq,hthresh] using hx.1
    have h1 := linf_center_subset (hn d) (fun x => residual x (Sstar d x)) (4*t) h0
    have h2 := sup_union_subset (hn d) (fun x => residual x (Sstar d x)) (4*t/2) h1
    have h3 := linf_loo_union_subset hd.2.1 (Sstar d) (hStar d) (Sdel d)
      (fun j x => (hSdel d j).2.1 x) (4*t/2) h2
    rw [Set.mem_iUnion] at h3 ⊢
    obtain ⟨j,hj⟩ := h3
    refine ⟨j,?_⟩
    simp only [Set.mem_ofPred_eq] at hj ⊢
    have hKlev : K+1 ≤ t := hlev.2.1
    linarith
  have hf := linf_onGood_union_tail hd.1 (Sdel d) (hHWraw d)
    (K := K) (Tlvl := t+K) (by linarith) (Good d)
    (fun x hx j => hshift x hx j (Sdel d j x) ((hSdel d j).2.1 x))
  have hf' : (gaussianSampleLaw d (n d)).real (F ∩ Good d) ≤
      (n d:ℝ)*(2*Real.exp (-c*t^2)) := by
    have hmin : min (t^2) (t*Real.sqrt (d:ℝ)) = t^2 :=
      paper_log_hw_min c d hlev.2.2
    simpa only [F,add_sub_cancel_right,hmin,measureReal_def] using hf
  have hsplit : E ⊆ (E ∩ Good d) ∪ (Good d)ᶜ := by
    intro x hx
    by_cases hg : x ∈ Good d
    · exact Or.inl ⟨hx,hg⟩
    · exact Or.inr hg
  calc
    (gaussianSampleLaw d (n d)).real E ≤
        (gaussianSampleLaw d (n d)).real (E ∩ Good d)+
          (gaussianSampleLaw d (n d)).real (Good d)ᶜ :=
      (measureReal_mono hsplit).trans (measureReal_union_le _ _)
    _ ≤ (n d:ℝ)*(2*Real.exp (-c*t^2))+(gaussianSampleLaw d (n d)).real (Good d)ᶜ :=
      add_le_add ((measureReal_mono hsub).trans hf') (le_refl _)

end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_huber_centered_linf
