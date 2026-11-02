import AHHWordEncodings
import AHHGeneratingBound
import Mathlib.Data.List.OfFn

/-! Concrete word families and splitting interfaces for the AHH recurrence.
All combinatorial maps below operate on actual lists. The remaining analytic
hypotheses are stated at the individual word level, never as a final moment recurrence. -/
noncomputable section
open scoped BigOperators
namespace AHH
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {α : Type*}

/-- All words of a fixed length on a finite alphabet. -/
def words (α : Type*) [Fintype α] (n : ℕ) : Finset (List α) := by
  classical
  exact Finset.univ.image (fun f : Fin n → α => List.ofFn f)

@[simp] theorem mem_words [Fintype α] {n : ℕ} {w : List α} :
    w ∈ words α n ↔ w.length = n := by
  classical
  constructor
  · intro hw
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hw
    simp
  · intro hw
    subst n
    apply Finset.mem_image.mpr
    exact ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

/-- Unnormalized expected trace sum, for a supplied single-word weight. -/
def wordSum [Fintype α] (T : List α → ℝ) (n : ℕ) : ℝ := ∑ w ∈ words α n, T w

theorem wordSum_nonneg [Fintype α] (T : List α → ℝ) (hT : ∀ w, 0 ≤ T w) (n : ℕ) :
    0 ≤ wordSum T n := Finset.sum_nonneg (fun w _ => hT w)

/-- Unique first marker decomposition when the preceding blocks avoid that marker. -/
theorem first_marker_inj (s : α) {A B U V : List α}
    (hA : s ∉ A) (hB : s ∉ B) (h : A ++ s :: U = B ++ s :: V) :
    A = B ∧ U = V := by
  induction A generalizing B with
  | nil =>
      cases B with
      | nil => exact ⟨rfl, (List.cons.inj h).2⟩
      | cons b B =>
          have hb : s = b := (List.cons.inj h).1
          exact (hB (by simp [hb])).elim
  | cons a A ih =>
      cases B with
      | nil =>
          have ha : a = s := (List.cons.inj h).1
          exact (hA (by simp [ha])).elim
      | cons b B =>
          have hh := List.cons.inj h
          obtain ⟨hAB, hUV⟩ := ih (fun hs => hA (List.mem_cons_of_mem a hs))
            (fun hs => hB (List.mem_cons_of_mem b hs)) hh.2
          exact ⟨by rw [hh.1, hAB], hUV⟩

/-- Splitting just before the last occurrence of the first letter. -/
@[ext] structure WordSplit (α : Type*) where
  s : α
  L : List α
  R : List α
  L_head : L.head? = some s
  R_avoids : s ∉ R

namespace WordSplit

def original (d : WordSplit α) : List α := d.L ++ [d.s] ++ d.R

def pair (d : WordSplit α) : List α × List α := (d.L, d.R)

def shared (d : WordSplit α) : Prop := ∃ a, a ∈ d.L ∧ a ∈ d.R

theorem left_ne_nil (d : WordSplit α) : d.L ≠ [] := by
  intro h
  simpa [h] using d.L_head

theorem pair_injective : Function.Injective (pair : WordSplit α → List α × List α) := by
  intro d e h
  have hL : d.L = e.L := congrArg Prod.fst h
  have hR : d.R = e.R := congrArg Prod.snd h
  have hs : d.s = e.s := by
    have := congrArg List.head? hL
    simpa [d.L_head, e.L_head] using this
  exact WordSplit.ext hs hL hR

theorem original_head (d : WordSplit α) : d.original.head? = some d.s := by
  simp [original, d.L_head]

/-- Last occurrence splitting is unique, including its first letter. -/
theorem original_injective : Function.Injective (original : WordSplit α → List α) := by
  intro d e h
  have hs : d.s = e.s := by
    have hh := congrArg List.head? h
    simpa only [original_head, Option.some.injEq] using hh
  have hr : d.R.reverse ++ d.s :: d.L.reverse = e.R.reverse ++ d.s :: e.L.reverse := by
    have hh := congrArg List.reverse h
    simpa [original, List.reverse_append, List.append_assoc, hs] using hh
  have hd : d.s ∉ d.R.reverse := by simpa using d.R_avoids
  have he : d.s ∉ e.R.reverse := by simpa [hs] using e.R_avoids
  obtain ⟨hR, hL⟩ := first_marker_inj d.s hd he hr
  exact WordSplit.ext hs (List.reverse_inj.mp hL) (List.reverse_inj.mp hR)

theorem exists_last_split (s : α) (w : List α) (h : s ∈ w) :
    ∃ L R, w = L ++ [s] ++ R ∧ s ∉ R := by
  classical
  induction w with
  | nil => simp at h
  | cons a w ih =>
      by_cases hw : s ∈ w
      · obtain ⟨L, R, hr, ha⟩ := ih hw
        exact ⟨a :: L, R, by simp [hr], ha⟩
      · have ha : a = s := by simpa [hw, eq_comm] using h
        subst a
        exact ⟨[], w, by simp, hw⟩

/-- Every word with a repeated first letter has an actual admissible last split. -/
theorem exists_of_repeated (s : α) (tail : List α) (h : s ∈ tail) :
    ∃ d : WordSplit α, d.original = s :: tail := by
  obtain ⟨L, R, hr, ha⟩ := exists_last_split s tail h
  exact ⟨⟨s, s :: L, R, rfl, ha⟩, by simp [original, hr]⟩

/-- A shared split has an actual rank-one gluing record with exactly the original
left and right words. Its nonempty prefix is derived from avoidance, not assumed. -/
theorem exists_collision (d : WordSplit α) (h : d.shared) :
    ∃ c : Collision α, c.left = d.L ∧ c.right = d.R ∧ c.original = d.original := by
  obtain ⟨a, haL, haR⟩ := h
  obtain ⟨U, V, hL⟩ := List.mem_iff_append.mp haL
  obtain ⟨X, Y, hR⟩ := List.mem_iff_append.mp haR
  have hL' : U ++ [a] ++ V = d.L := by simpa using hL.symm
  have hR' : X ++ [a] ++ Y = d.R := by simpa using hR.symm
  let c := Collision.ofSplit d.s a U V X Y (by rw [hL']; exact d.L_head)
    (by rw [hR']; exact d.R_avoids)
  refine ⟨c, hL', hR', ?_⟩
  change (U ++ [a] ++ V) ++ [d.s] ++ (X ++ [a] ++ Y) = d.original
  rw [hL', hR']; rfl

/-- A deterministic gluing map is selected from the proved decomposition. -/
def collision (d : WordSplit α) (h : d.shared) : Collision α :=
  (exists_collision d h).choose

theorem collision_left (d : WordSplit α) (h : d.shared) : (d.collision h).left = d.L :=
  (exists_collision d h).choose_spec.1

theorem collision_right (d : WordSplit α) (h : d.shared) : (d.collision h).right = d.R :=
  (exists_collision d h).choose_spec.2.1

theorem collision_original (d : WordSplit α) (h : d.shared) :
    (d.collision h).original = d.original := (exists_collision d h).choose_spec.2.2

theorem collision_injective : Function.Injective
    (fun d : {d : WordSplit α // d.shared} => d.val.collision d.property) := by
  intro d e h
  apply Subtype.ext
  apply pair_injective
  apply Prod.ext
  · have := congrArg Collision.left h
    simpa only [collision_left, pair] using this
  · have := congrArg Collision.right h
    simpa only [collision_right, pair] using this

/-- The disjoint-word contribution is bounded by the precise truncated convolution.
This is a two-word injection, not an assumption about the moment recurrence. -/
theorem sum_split_product_le [Fintype α] (D : Finset (WordSplit α))
    (T : List α → ℝ) (hT : ∀ w, 0 ≤ T w) (n : ℕ)
    (hlen : ∀ d ∈ D, d.L.length + d.R.length = n) :
    (∑ d ∈ D, T d.L * T d.R) ≤
      ∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l) := by
  classical
  have heq : (∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l)) =
      ∑ q ∈ (Finset.range n).sigma
        (fun l => (words α (n - l)).product (words α l)), T q.2.1 * T q.2.2 := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro l hl
    dsimp
    rw [Finset.sum_product]
    dsimp [wordSum]
    rw [mul_comm, Finset.sum_mul_sum]
  rw [heq]
  apply Finset.sum_le_sum_of_injOn
    (fun d : WordSplit α => (⟨d.R.length, (d.L, d.R)⟩ : Σ _ : ℕ, List α × List α))
  · intro d _ e _ h
    apply pair_injective
    have hh := Sigma.mk.inj_iff.mp h
    exact eq_of_heq hh.2
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_sigma.mpr
    dsimp
    have hn := hlen d hd
    have hL : 0 < d.L.length := List.length_pos_iff.mpr d.left_ne_nil
    constructor
    · apply Finset.mem_range.mpr; omega
    · apply Finset.mem_product.mpr
      constructor <;> apply mem_words.mpr <;> dsimp
      · omega
  · intro d _; rfl
  · intro q _ _; exact mul_nonneg (hT _) (hT _)

/-- Shared split traces are charged to ordinary words using the verified three-cut map. -/
theorem sum_shared_le [Fintype α] (D : Finset {d : WordSplit α // d.shared})
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output) (n : ℕ)
    (hlen : ∀ d ∈ D, d.val.L.length + d.val.R.length = n) :
    (∑ d ∈ D, S d.val.L d.val.R) ≤ (n + 1 : ℕ) ^ 3 * wordSum T n := by
  classical
  let f : {d : WordSplit α // d.shared} → Collision α := fun d => d.val.collision d.property
  have hsum : (∑ d ∈ D, S d.val.L d.val.R) = ∑ c ∈ D.image f, T c.output := by
    rw [Finset.sum_image (fun d _ e _ h => collision_injective h)]
    apply Finset.sum_congr rfl
    intro d hd
    have h := hmerge (f d)
    simpa [f, collision_left, collision_right] using h
  rw [hsum]
  apply Collision.sum_output_le _ (words α n) n T hT
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    apply mem_words.mpr
    have hlen' := congrArg List.length (collision_original d.val d.property)
    have hc := Collision.original_length (f d)
    have hdlen := hlen d hd
    change (f d).original.length = d.val.original.length at hlen'
    simp only [original, List.length_append, List.length_singleton] at hlen'
    omega
  · intro w hw; exact mem_words.mp hw

/-- The complete split contribution, classified by actual shared letters. -/
theorem sum_split_le [Fintype α] (D : Finset (WordSplit α))
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → S d.L d.R = T d.L * T d.R)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output) (n : ℕ)
    (hlen : ∀ d ∈ D, d.L.length + d.R.length = n) :
    (∑ d ∈ D, S d.L d.R) ≤
      (∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l)) +
        (n + 1 : ℕ) ^ 3 * wordSum T n := by
  classical
  have hs := sum_shared_le (D.subtype shared) T S hT hmerge n
    (fun d hd => hlen d.val (Finset.mem_subtype.mp hd))
  rw [Finset.sum_subtype_eq_sum_filter (fun d : WordSplit α => S d.L d.R)] at hs
  have hd : (∑ d ∈ D.filter (fun d => ¬ d.shared), S d.L d.R) ≤
      ∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l) := by
    calc
      _ = ∑ d ∈ D.filter (fun d => ¬ d.shared), T d.L * T d.R := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hdisjoint d (Finset.mem_filter.mp hd).2
      _ ≤ _ := sum_split_product_le _ T hT n
        (fun d hd => hlen d (Finset.mem_filter.mp hd).1)
  have heq := Finset.sum_filter_add_sum_filter_not D shared (fun d => S d.L d.R)
  linarith

/-- All rearrangement terms from distinct last splits are distinct records.
The proof derives this from their original words, then uses the two-cut bound. -/
theorem sum_moves_le [Fintype α] (D : Finset (WordSplit α))
    (moves : WordSplit α → Finset (Rearrangement α))
    (hmoves : ∀ d ∈ D, ∀ r ∈ moves d, r.original = d.original)
    (T : List α → ℝ) (hT : ∀ w, 0 ≤ T w) (n : ℕ)
    (hlen : ∀ d ∈ D, d.L.length + d.R.length = n) :
    (∑ d ∈ D, ∑ r ∈ moves d, T r.output) ≤ (n + 1 : ℕ) ^ 2 * wordSum T n := by
  classical
  have hdis : (D : Set (WordSplit α)).Pairwise
      (fun d e => Disjoint (moves d) (moves e)) := by
    intro d hd e he hne
    apply Finset.disjoint_left.mpr
    intro r hrd hre
    apply hne
    apply original_injective
    exact (hmoves d hd r hrd).symm.trans (hmoves e he r hre)
  rw [← Finset.sum_biUnion hdis]
  apply Rearrangement.sum_output_le _ (words α n) n T hT
  · intro r hr
    obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hr
    apply mem_words.mpr
    have ho := congrArg List.length (hmoves d hd r hrd)
    have hl := hlen d hd
    have hrlen := Rearrangement.original_length r
    simp only [original, List.length_append, List.length_singleton] at ho
    omega
  · intro w hw; exact mem_words.mp hw

/-- Local repeated-word elimination plus actual word encodings gives its summed bound. -/
theorem sum_repeated_le [Fintype α] (D : Finset (WordSplit α))
    (moves : WordSplit α → Finset (Rearrangement α))
    (hmoves : ∀ d ∈ D, ∀ r ∈ moves d, r.original = d.original)
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → S d.L d.R = T d.L * T d.R)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output)
    {c k : ℝ} (hc : 0 ≤ c) (hk : 0 ≤ k) (n : ℕ)
    (hlen : ∀ d ∈ D, d.L.length + d.R.length = n)
    (helim : ∀ d ∈ D, T d.original ≤ c * S d.L d.R + k * ∑ r ∈ moves d, T r.output) :
    (∑ d ∈ D, T d.original) ≤
      c * (∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l)) +
        (k * (n + 1 : ℕ) ^ 2 + c * (n + 1 : ℕ) ^ 3) * wordSum T n := by
  have hsplit := sum_split_le D T S hT hdisjoint hmerge n hlen
  have hmove := sum_moves_le D moves hmoves T hT n hlen
  calc
    _ ≤ ∑ d ∈ D, (c * S d.L d.R + k * ∑ r ∈ moves d, T r.output) :=
      Finset.sum_le_sum helim
    _ = c * (∑ d ∈ D, S d.L d.R) + k * (∑ d ∈ D, ∑ r ∈ moves d, T r.output) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ c * ((∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l)) +
        (n + 1 : ℕ) ^ 3 * wordSum T n) + k * ((n + 1 : ℕ) ^ 2 * wordSum T n) :=
      add_le_add (mul_le_mul_of_nonneg_left hsplit hc) (mul_le_mul_of_nonneg_left hmove hk)
    _ = _ := by ring

end WordSplit

/-- A word whose first letter occurs again. -/
abbrev RepeatedWord (α : Type*) := {q : α × List α // q.1 ∈ q.2}

namespace RepeatedWord

def split (q : RepeatedWord α) : WordSplit α :=
  (WordSplit.exists_of_repeated q.val.1 q.val.2 q.property).choose

theorem split_original (q : RepeatedWord α) : q.split.original = q.val.1 :: q.val.2 :=
  (WordSplit.exists_of_repeated q.val.1 q.val.2 q.property).choose_spec

theorem split_injective : Function.Injective (split : RepeatedWord α → WordSplit α) := by
  intro q r h
  have hh := congrArg WordSplit.original h
  simp only [split_original, List.cons.injEq] at hh
  apply Subtype.ext
  exact Prod.ext hh.1 hh.2

end RepeatedWord

/-- Canonical last splits of every length-`n+1` word with a repeated first letter. -/
def repeatedSplits (α : Type*) [Fintype α] (n : ℕ) : Finset (WordSplit α) := by
  classical
  exact (((Finset.univ : Finset α).product (words α n)).subtype
    (fun q : α × List α => q.1 ∈ q.2)).image RepeatedWord.split

theorem repeatedSplits_length [Fintype α] (n : ℕ) (d : WordSplit α)
    (hd : d ∈ repeatedSplits α n) : d.L.length + d.R.length = n := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
  have hw := (Finset.mem_product.mp (Finset.mem_subtype.mp hq)).2
  have hl := mem_words.mp hw
  have ho := congrArg List.length (RepeatedWord.split_original q)
  simp [WordSplit.original] at ho
  omega

/-- Expansion of a word sum by its actual first letter and remaining tail. -/
theorem wordSum_succ [Fintype α] (T : List α → ℝ) (n : ℕ) :
    wordSum T (n + 1) = ∑ q ∈ (Finset.univ : Finset α).product (words α n), T (q.1 :: q.2) := by
  classical
  have hi : words α (n + 1) = ((Finset.univ : Finset α).product (words α n)).image
      (fun q : α × List α => q.1 :: q.2) := by
    ext w
    cases w with
    | nil => simp [mem_words]
    | cons a w => simp [mem_words]
  rw [wordSum, hi, Finset.sum_image]
  intro q _ r _ h
  exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

/-- The repeated-letter summands are exactly the canonical last-split summands. -/
theorem sum_repeated_eq [Fintype α] (T : List α → ℝ) (n : ℕ) :
    (∑ q ∈ ((Finset.univ : Finset α).product (words α n)).filter
      (fun q : α × List α => q.1 ∈ q.2), T (q.1 :: q.2)) =
    ∑ d ∈ repeatedSplits α n, T d.original := by
  classical
  rw [repeatedSplits, Finset.sum_image (fun q _ r _ h => RepeatedWord.split_injective h)]
  simp only [RepeatedWord.split_original]
  simpa using (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α).product (words α n))
    (p := fun q : α × List α => q.1 ∈ q.2) (fun q : α × List α => T (q.1 :: q.2))).symm

/-- Unique-first-letter integration is summed by extending a positive sum to all tails. -/
theorem sum_unique_le [Fintype α] (T : List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    {q : ℝ} (hq : 0 ≤ q) (n : ℕ)
    (hsingle : ∀ s : α, ∀ w ∈ words α n, s ∉ w → T (s :: w) = q * T w) :
    (∑ v ∈ ((Finset.univ : Finset α).product (words α n)).filter
      (fun v : α × List α => v.1 ∉ v.2), T (v.1 :: v.2)) ≤
      Fintype.card α * q * wordSum T n := by
  classical
  calc
    _ = ∑ v ∈ ((Finset.univ : Finset α).product (words α n)).filter
        (fun v : α × List α => v.1 ∉ v.2), q * T v.2 := by
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hv, hn⟩ := Finset.mem_filter.mp hv
      exact hsingle v.1 v.2 (Finset.mem_product.mp hv).2 hn
    _ ≤ ∑ v ∈ (Finset.univ : Finset α).product (words α n), q * T v.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v _ _; exact mul_nonneg hq (hT _)
    _ = _ := by
      have hp := Finset.sum_product' (Finset.univ : Finset α) (words α n)
        (fun (_ : α) (w : List α) => q * T w)
      calc
        _ = ∑ _s ∈ (Finset.univ : Finset α), ∑ w ∈ words α n, q * T w := hp
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
        wordSum, mul_assoc]

/-- Full unnormalized word recurrence, derived from single-word analytic identities
and the explicit two/three-cut combinatorics. The recurrence itself is not a premise. -/
theorem word_recurrence [Fintype α]
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → S d.L d.R = T d.L * T d.R)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output)
    (moves : WordSplit α → Finset (Rearrangement α))
    (n : ℕ) (hmoves : ∀ d ∈ repeatedSplits α n, ∀ r ∈ moves d, r.original = d.original)
    {q c k : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hsingle : ∀ s : α, ∀ w ∈ words α n, s ∉ w → T (s :: w) = q * T w)
    (helim : ∀ d ∈ repeatedSplits α n,
      T d.original ≤ c * S d.L d.R + k * ∑ r ∈ moves d, T r.output) :
    wordSum T (n + 1) ≤ c * (∑ l ∈ Finset.range n, wordSum T l * wordSum T (n - l)) +
      (Fintype.card α * q + k * (n + 1 : ℕ) ^ 2 + c * (n + 1 : ℕ) ^ 3) * wordSum T n := by
  classical
  have hu := sum_unique_le T hT hq n hsingle
  have hr := WordSplit.sum_repeated_le (repeatedSplits α n) moves hmoves T S hT
    hdisjoint hmerge hc hk n (repeatedSplits_length n) helim
  rw [← sum_repeated_eq T n] at hr
  have hs := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset α).product (words α n)) (fun q : α × List α => q.1 ∈ q.2)
    (fun q => T (q.1 :: q.2))
  rw [wordSum_succ]
  nlinarith

end AHH
