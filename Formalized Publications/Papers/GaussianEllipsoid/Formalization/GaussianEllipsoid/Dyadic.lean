/-
Copyright (c) 2026 Aykut Arslan.
Kernel-checked repaired dyadic construction.

This file repairs the coordinate/level intersection in paper.tex:1801-1805.
A level selector is a Set Nat; a coordinate support is a Finset I.
The selector is applied to the level BEFORE taking the union of coordinate bins.
No probabilistic or support-record existence theorem is asserted here.
-/
import Mathlib

noncomputable section

namespace GaussianEllipsoid
namespace Dyadic

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Actual magnitude bin at level t, with a separately supplied positive scale. -/
def bin (u : I -> Real) (scale : Real) (t : Nat) : Finset I :=
  Finset.univ.filter (fun i => scale / (2 : Real) ^ (t + 1) < |u i| /\
    |u i| <= scale / (2 : Real) ^ t)

omit [DecidableEq I] in
@[simp] theorem mem_bin (u : I -> Real) (scale : Real) (t : Nat) (i : I) :
    i ∈ bin u scale t <->
      scale / (2 : Real) ^ (t + 1) < |u i| /\
      |u i| <= scale / (2 : Real) ^ t := by
  simp [bin]

/-- Finite coordinates whose bin level belongs to the specified level set. -/
def levelCoords (bins : Nat -> Finset I) (levels : Set Nat) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => exists t : Nat, t ∈ levels /\ i ∈ bins t)

omit [DecidableEq I] in
@[simp] theorem mem_levelCoords (bins : Nat -> Finset I) (levels : Set Nat) (i : I) :
    i ∈ levelCoords bins levels <-> exists t : Nat, t ∈ levels /\ i ∈ bins t := by
  classical
  simp [levelCoords]

/-- Corrected retained support. Only the level t is compared with the cutoff. -/
def retainedCoords (bins : Nat -> Finset I) (group : Set Nat)
    (start depth : Nat) : Finset I :=
  levelCoords bins {t | t ∈ group /\ t < start + depth}

/-- Corrected omitted support. The group already specifies its lower endpoint. -/
def omittedCoords (bins : Nat -> Finset I) (group : Set Nat)
    (start depth : Nat) : Finset I :=
  levelCoords bins {t | t ∈ group /\ start + depth <= t}

/-- Pairwise disjointness of the bins is the sole uniqueness hypothesis. -/
def DisjointBins (bins : Nat -> Finset I) : Prop :=
  forall s t : Nat, s ≠ t -> Disjoint (bins s) (bins t)

omit [Fintype I] [DecidableEq I] in
theorem levels_eq_of_mem {bins : Nat -> Finset I} (h : DisjointBins bins)
    {s t : Nat} {i : I} (hs : i ∈ bins s) (ht : i ∈ bins t) : s = t := by
  by_contra hne
  exact Finset.disjoint_left.mp (h s t hne) hs ht

omit [DecidableEq I] in
theorem levelCoords_mono {bins : Nat -> Finset I} {A B : Set Nat}
    (hAB : A ⊆ B) : levelCoords bins A ⊆ levelCoords bins B := by
  intro i hi
  have hw := (mem_levelCoords _ _ _).mp hi
  let t := hw.choose
  have ht := hw.choose_spec.1
  have hit := hw.choose_spec.2
  exact (mem_levelCoords _ _ _).mpr (Exists.intro t (And.intro (hAB ht) hit))

omit [DecidableEq I] in
theorem levelCoords_disjoint {bins : Nat -> Finset I} (hb : DisjointBins bins)
    {A B : Set Nat} (hAB : Disjoint A B) :
    Disjoint (levelCoords bins A) (levelCoords bins B) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hw := (mem_levelCoords _ _ _).mp hi
  have hz := (mem_levelCoords _ _ _).mp hj
  let s := hw.choose
  let t := hz.choose
  have hs := hw.choose_spec.1
  have his := hw.choose_spec.2
  have ht := hz.choose_spec.1
  have hit := hz.choose_spec.2
  have hst := levels_eq_of_mem hb his hit
  apply Set.disjoint_left.mp hAB hs
  simpa only [hst] using ht

/-- Every group coordinate is either retained or omitted, even for an infinite last group. -/
theorem retained_union_omitted (bins : Nat -> Finset I) (group : Set Nat)
    (start depth : Nat) :
    retainedCoords bins group start depth ∪ omittedCoords bins group start depth =
      levelCoords bins group := by
  classical
  ext i
  simp only [Finset.mem_union, retainedCoords, omittedCoords, mem_levelCoords,
    Set.mem_ofPred_eq]
  constructor
  next =>
    intro hw
    apply Or.elim hw
    next =>
      intro hw
      exact Exists.intro hw.choose (And.intro hw.choose_spec.1.1 hw.choose_spec.2)
    next =>
      intro hw
      exact Exists.intro hw.choose (And.intro hw.choose_spec.1.1 hw.choose_spec.2)
  next =>
    intro hw
    let t := hw.choose
    have ht := hw.choose_spec.1
    have hi := hw.choose_spec.2
    by_cases hcut : t < start + depth
    next => exact Or.inl (Exists.intro t (And.intro (And.intro ht hcut) hi))
    next => exact Or.inr (Exists.intro t
      (And.intro (And.intro ht (Nat.le_of_not_gt hcut)) hi))

omit [DecidableEq I] in
theorem retained_disjoint_omitted {bins : Nat -> Finset I} (hb : DisjointBins bins)
    (group : Set Nat) (start depth : Nat) :
    Disjoint (retainedCoords bins group start depth)
      (omittedCoords bins group start depth) := by
  apply levelCoords_disjoint hb
  apply Set.disjoint_left.mpr
  intro t ht hu
  exact Nat.not_lt_of_ge hu.2 ht.2

omit [DecidableEq I] in
theorem base_bin_subset_retained (bins : Nat -> Finset I) {group : Set Nat}
    {start depth : Nat} (hstart : start ∈ group) (hdepth : 0 < depth) :
    bins start ⊆ retainedCoords bins group start depth := by
  intro i hi
  apply (mem_levelCoords _ _ _).mpr
  exact Exists.intro start (And.intro (And.intro hstart (by omega)) hi)

omit [DecidableEq I] in
/-- Different record groups retain disjoint coordinate supports. -/
theorem retained_disjoint_of_groups {bins : Nat -> Finset I} (hb : DisjointBins bins)
    {A B : Set Nat} (hAB : Disjoint A B) (s t depth : Nat) :
    Disjoint (retainedCoords bins A s depth) (retainedCoords bins B t depth) := by
  apply levelCoords_disjoint hb
  apply Set.disjoint_left.mpr
  intro k hk hl
  exact Set.disjoint_left.mp hAB hk.1 hl.1

/-- Restriction to a finite coordinate set. -/
def restrict (u : I -> Real) (A : Finset I) : I -> Real :=
  fun i => if i ∈ A then u i else 0

/-- Finite support, with no choice of norm representation. -/
def support (u : I -> Real) : Finset I :=
  Finset.univ.filter (fun i => u i ≠ 0)

omit [DecidableEq I] in
@[simp] theorem mem_support (u : I -> Real) (i : I) :
    i ∈ support u <-> u i ≠ 0 := by
  simp [support]

@[simp] theorem support_restrict (u : I -> Real) (A : Finset I) :
    support (restrict u A) = A ∩ support u := by
  classical
  ext i
  by_cases hi : i ∈ A <;> simp [support, restrict, hi]

omit [Fintype I] in
theorem restrict_union (u : I -> Real) {A B : Finset I} (hAB : Disjoint A B) :
    restrict u (A ∪ B) = fun i => restrict u A i + restrict u B i := by
  funext i
  by_cases hi : i ∈ A
  next =>
    have hj : i ∉ B := fun hj => Finset.disjoint_left.mp hAB hi hj
    simp [restrict, hi, hj, Finset.mem_union]
  next =>
    by_cases hj : i ∈ B <;> simp [restrict, hi, hj, Finset.mem_union]

/-- The repaired construction gives the exact within-group vector decomposition. -/
theorem group_restriction_decomposition {bins : Nat -> Finset I}
    (hb : DisjointBins bins) (u : I -> Real) (group : Set Nat) (start depth : Nat) :
    restrict u (levelCoords bins group) = fun i =>
      restrict u (retainedCoords bins group start depth) i +
      restrict u (omittedCoords bins group start depth) i := by
  rw [<- retained_union_omitted bins group start depth]
  exact restrict_union u (retained_disjoint_omitted hb group start depth)

/-- A nonzero coordinate in the base bin survives the repaired restriction. -/
theorem base_bin_subset_support {bins : Nat -> Finset I} (u : I -> Real)
    {group : Set Nat} {start depth : Nat} (hstart : start ∈ group) (hdepth : 0 < depth)
    (hnz : forall i, i ∈ bins start -> u i ≠ 0) :
    bins start ⊆ support (restrict u (retainedCoords bins group start depth)) := by
  intro i hi
  rw [support_restrict]
  exact Finset.mem_inter.mpr
    (And.intro (base_bin_subset_retained bins hstart hdepth hi)
      ((mem_support _ _).mpr (hnz i hi)))

/-- l1 mass of finitely many coordinates. -/
def mass (u : I -> Real) (A : Finset I) : Real :=
  A.sum (fun i => |u i|)

/-- Squared Euclidean mass of finitely many coordinates. -/
def energy (u : I -> Real) (A : Finset I) : Real :=
  A.sum (fun i => (u i) ^ 2)

omit [Fintype I] [DecidableEq I] in
theorem mass_pos {u : I -> Real} {A : Finset I}
    (h : exists i, i ∈ A /\ u i ≠ 0) : 0 < mass u A := by
  let i := h.choose
  have hi := h.choose_spec.1
  have hu := h.choose_spec.2
  exact Finset.sum_pos' (fun j _ => abs_nonneg (u j))
    (Exists.intro i (And.intro hi (abs_pos.mpr hu)))

omit [Fintype I] [DecidableEq I] in
theorem energy_pos {u : I -> Real} {A : Finset I}
    (h : exists i, i ∈ A /\ u i ≠ 0) : 0 < energy u A := by
  let i := h.choose
  have hi := h.choose_spec.1
  have hu := h.choose_spec.2
  exact Finset.sum_pos' (fun j _ => sq_nonneg (u j))
    (Exists.intro i (And.intro hi (sq_pos_of_ne_zero hu)))

omit [DecidableEq I] in
/-- Genuine dyadic-bin members are nonzero when the scale is positive. -/
theorem nonzero_of_mem_bin {u : I -> Real} {scale : Real} (hscale : 0 < scale)
    {t : Nat} {i : I} (hi : i ∈ bin u scale t) : u i ≠ 0 := by
  have hi' := (mem_bin _ _ _ _).mp hi
  have hpos : 0 < scale / (2 : Real) ^ (t + 1) := by positivity
  exact abs_pos.mp (lt_trans hpos hi'.1)

omit [DecidableEq I] in
/-- Actual dyadic bins have disjoint supports. Boundary equality belongs only to the later bin. -/
theorem bins_disjoint (u : I -> Real) {scale : Real} (hscale : 0 <= scale) :
    DisjointBins (bin u scale) := by
  intro s t hst
  apply Finset.disjoint_left.mpr
  intro i his hit
  have hs := (mem_bin _ _ _ _).mp his
  have ht := (mem_bin _ _ _ _).mp hit
  rcases lt_or_gt_of_ne hst with hlt | hgt
  next =>
    have hexp : (2 : Real) ^ (s + 1) <= (2 : Real) ^ t :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdiv : scale / (2 : Real) ^ t <= scale / (2 : Real) ^ (s + 1) :=
      div_le_div_of_nonneg_left hscale (by positivity) hexp
    linarith
  next =>
    have hexp : (2 : Real) ^ (t + 1) <= (2 : Real) ^ s :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdiv : scale / (2 : Real) ^ s <= scale / (2 : Real) ^ (t + 1) :=
      div_le_div_of_nonneg_left hscale (by positivity) hexp
    linarith

/-- At a positive scale, the retained coordinate set is exactly the vector's retained support. -/
theorem support_retained_eq {u : I -> Real} {scale : Real} (hscale : 0 < scale)
    (group : Set Nat) (start depth : Nat) :
    support (restrict u (retainedCoords (bin u scale) group start depth)) =
      retainedCoords (bin u scale) group start depth := by
  rw [support_restrict]
  ext i
  simp only [Finset.mem_inter, mem_support]
  constructor
  next => exact And.left
  next =>
    intro hi
    have hw := (mem_levelCoords _ _ _).mp hi
    exact And.intro hi (nonzero_of_mem_bin hscale hw.choose_spec.2)

omit [DecidableEq I] in
/-- Every nonzero coefficient below the scale belongs to a dyadic bin. -/
theorem exists_mem_bin {u : I -> Real} {scale : Real} (hscale : 0 < scale)
    {i : I} (hnz : u i ≠ 0) (hbound : |u i| <= scale) :
    exists t : Nat, i ∈ bin u scale t := by
  have hx : 0 < |u i| / scale := div_pos (abs_pos.mpr hnz) hscale
  have hxone : |u i| / scale <= 1 := by
    calc
      |u i| / scale <= scale / scale := div_le_div_of_nonneg_right hbound hscale.le
      _ = 1 := div_self (ne_of_gt hscale)
  have hw := exists_nat_pow_near_of_lt_one hx hxone
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) < 1)
  let t := hw.choose
  have ht := hw.choose_spec
  have hcancel : |u i| / scale * scale = |u i| := by field_simp [ne_of_gt hscale]
  refine Exists.intro t ((mem_bin _ _ _ _).mpr (And.intro ?_ ?_))
  next =>
    calc
      scale / (2 : Real) ^ (t + 1) = (1 / 2 : Real) ^ (t + 1) * scale := by
        simp [div_eq_mul_inv, mul_comm]
      _ < |u i| / scale * scale := mul_lt_mul_of_pos_right ht.1 hscale
      _ = |u i| := hcancel
  next =>
    calc
      |u i| = |u i| / scale * scale := hcancel.symm
      _ <= (1 / 2 : Real) ^ t * scale := mul_le_mul_of_nonneg_right ht.2 hscale.le
      _ = scale / (2 : Real) ^ t := by simp [div_eq_mul_inv, mul_comm]

omit [DecidableEq I] in
/-- The actual bins partition the finite support for any valid positive upper scale. -/
theorem all_levels_eq_support (u : I -> Real) {scale : Real} (hscale : 0 < scale)
    (hbound : forall i, |u i| <= scale) :
    levelCoords (bin u scale) Set.univ = support u := by
  ext i
  constructor
  next =>
    intro hi
    have hw := (mem_levelCoords _ _ _).mp hi
    exact (mem_support _ _).mpr (nonzero_of_mem_bin hscale hw.choose_spec.2)
  next =>
    intro hi
    have hw := exists_mem_bin hscale ((mem_support _ _).mp hi) (hbound i)
    exact (mem_levelCoords _ _ _).mpr
      (Exists.intro hw.choose (And.intro (Set.mem_univ _) hw.choose_spec))

/-- A finite vector is unchanged by restricting it to its support. -/
theorem restrict_support (u : I -> Real) : restrict u (support u) = u := by
  funext i
  by_cases hi : u i = 0 <;> simp [restrict, support, hi]

/-- The repaired all-level construction gives a literal coefficient-vector split. -/
theorem all_level_decomposition (u : I -> Real) {scale : Real} (hscale : 0 < scale)
    (hbound : forall i, |u i| <= scale) (depth : Nat) :
    u = fun i => restrict u (retainedCoords (bin u scale) Set.univ 0 depth) i +
      restrict u (omittedCoords (bin u scale) Set.univ 0 depth) i := by
  have h := group_restriction_decomposition (bins_disjoint u hscale.le)
    u Set.univ 0 depth
  rw [all_levels_eq_support u hscale hbound, restrict_support] at h
  exact h

omit [DecidableEq I] in
/-- Positivity of both retained masses follows from a nonempty base bin. -/
theorem retained_mass_energy_pos {u : I -> Real} {scale : Real} (hscale : 0 < scale)
    {group : Set Nat} {start depth : Nat} (hstart : start ∈ group) (hdepth : 0 < depth)
    (hbase : (bin u scale start).Nonempty) :
    0 < mass u (retainedCoords (bin u scale) group start depth) /\
    0 < energy u (retainedCoords (bin u scale) group start depth) := by
  let i := hbase.choose
  have hi := hbase.choose_spec
  have hw : exists i, i ∈ retainedCoords (bin u scale) group start depth /\ u i ≠ 0 :=
    Exists.intro i (And.intro (base_bin_subset_retained _ hstart hdepth hi)
      (nonzero_of_mem_bin hscale hi))
  exact And.intro (mass_pos hw) (energy_pos hw)

/-- The Pi norm on finite real coordinate functions is exactly the sup norm used by the paper. -/
def maxScale (u : I -> Real) : Real := norm u

omit [DecidableEq I] in
theorem abs_le_maxScale (u : I -> Real) (i : I) : |u i| <= maxScale u := by
  simpa only [maxScale, Real.norm_eq_abs] using norm_le_pi_norm u i

omit [DecidableEq I] in
theorem maxScale_pos {u : I -> Real} (hu : u ≠ 0) : 0 < maxScale u :=
  norm_pos_iff.mpr hu

omit [DecidableEq I] in
/-- The actual bins at the paper's max-coefficient scale partition support(u). -/
theorem paper_bins_partition {u : I -> Real} (hu : u ≠ 0) :
    levelCoords (bin u (maxScale u)) Set.univ = support u :=
  all_levels_eq_support u (maxScale_pos hu) (abs_le_maxScale u)

/-- The source counterexample uses 1-based nonzero coordinate labels inside Fin 4. -/
def sourceExample (i : Fin 4) : Real :=
  if i.val = 1 then 1 else if i.val = 2 ∨ i.val = 3 then 2 / 5 else 0

/-- The literal source intersection mistakenly applies the level set {0} to coordinate labels. -/
def literalExample : Finset (Fin 4) :=
  (bin sourceExample 1 0).filter (fun i => i.val = 0)

theorem sourceExample_bin_zero : bin sourceExample 1 0 = {1} := by
  ext i
  fin_cases i <;> norm_num [bin, sourceExample]

theorem sourceExample_bin_one : bin sourceExample 1 1 = {2, 3} := by
  ext i
  fin_cases i <;> norm_num [bin, sourceExample] <;> decide

theorem sourceExample_record_growth :
    2 * (bin sourceExample 1 0).card = (bin sourceExample 1 1).card := by
  rw [sourceExample_bin_zero, sourceExample_bin_one]
  decide

theorem literalExample_empty : literalExample = Finset.empty := by
  rw [literalExample, sourceExample_bin_zero]
  decide

/-- Repaired construction: the corrected level restriction preserves the nonempty base bin. -/
theorem repairedExample :
    retainedCoords (bin sourceExample 1) ({0} : Set Nat) 0 1 = {1} := by
  classical
  rw [<- sourceExample_bin_zero]
  ext i
  simp [retainedCoords, mem_levelCoords]

/-- The literal construction has zero mass, contradicting the claimed positive base mass. -/
theorem literalExample_mass_zero : mass sourceExample literalExample = 0 := by
  rw [literalExample_empty]
  unfold mass
  exact Finset.sum_empty

theorem repairedExample_mass_one :
    mass sourceExample (retainedCoords (bin sourceExample 1) ({0} : Set Nat) 0 1) = 1 := by
  rw [repairedExample]
  norm_num [mass, sourceExample]

end Dyadic
end GaussianEllipsoid
