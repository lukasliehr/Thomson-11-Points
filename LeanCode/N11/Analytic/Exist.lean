module

public import N11.Analytic.Potential
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The theorem for 11 points, analytic part: a minimizer exists (row A3)

`Kset δ2` is the set of configurations of the sphere whose points have pairwise squared distances at least `δ2`.
It is closed and contained in a product of intervals, hence compact, and the energy is continuous on it if
`δ2 > 0` (`isCompact_Kset`, `continuousOn_energy`).

`exists_minimizer`: if some configuration of distinct points of the sphere has energy at most `B`, then the energy
has a minimizer among all configurations of distinct points of the sphere. Every pair of points of a configuration
with energy at most `B` has the squared distance at least `1/B²` (`sep_of_energy_le`), so a configuration with less
energy than the minimizer of `Kset (1/B²)` would lie in `Kset (1/B²)`.
-/

@[expose] public section

namespace N11.Analytic

open Finset

/-- The configurations of the sphere whose points have pairwise squared distances at least `δ2`. -/
def Kset (δ2 : ℝ) : Set (Fin 11 → Fin 3 → ℝ) :=
  {x | (∀ i, ∑ k, x i k ^ 2 = 1) ∧ ∀ i j, i ≠ j → δ2 ≤ ∑ k, (x i k - x j k) ^ 2}

theorem isClosed_Kset (δ2 : ℝ) : IsClosed (Kset δ2) := by
  have e : Kset δ2 = (⋂ i, {x : Fin 11 → Fin 3 → ℝ | ∑ k, x i k ^ 2 = 1}) ∩
      ⋂ i, ⋂ j, {x : Fin 11 → Fin 3 → ℝ | i ≠ j → δ2 ≤ ∑ k, (x i k - x j k) ^ 2} := by
    ext x
    simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_eq (by fun_prop) (by fun_prop))
    (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  by_cases h : i = j
  · have e2 : {x : Fin 11 → Fin 3 → ℝ | i ≠ j → δ2 ≤ ∑ k, (x i k - x j k) ^ 2} = Set.univ := by
      ext x
      simp [h]
    rw [e2]
    exact isClosed_univ
  · have e2 : {x : Fin 11 → Fin 3 → ℝ | i ≠ j → δ2 ≤ ∑ k, (x i k - x j k) ^ 2}
        = {x : Fin 11 → Fin 3 → ℝ | δ2 ≤ ∑ k, (x i k - x j k) ^ 2} := by
      ext x
      simp [h]
    rw [e2]
    exact isClosed_le continuous_const (by fun_prop)

theorem isCompact_Kset (δ2 : ℝ) : IsCompact (Kset δ2) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 11 => Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset (isClosed_Kset δ2) ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i k
  have h1 := hx.1 i
  have h2 : x i k ^ 2 ≤ 1 ^ 2 := by
    rw [one_pow, ← h1]
    exact single_le_sum (f := fun k => x i k ^ 2) (fun k _ => sq_nonneg _) (mem_univ k)
  exact abs_le.mp (abs_le_of_sq_le_sq h2 zero_le_one)

theorem continuousOn_energy {δ2 : ℝ} (hδ : 0 < δ2) : ContinuousOn energy (Kset δ2) := by
  unfold energy
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (mem_filter.mp hj).2
  refine ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop)) fun x hx => ?_
  exact (Real.sqrt_pos.mpr (lt_of_lt_of_le hδ (hx.2 i j hij))).ne'

/-- One term of the energy is at most the energy. -/
theorem term_le_energy (x : Fin 11 → Fin 3 → ℝ) {i j : Fin 11} (hij : i < j) :
    1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2) ≤ energy x := by
  unfold energy
  have hnn : ∀ a b : Fin 11, 0 ≤ 1 / Real.sqrt (∑ k, (x a k - x b k) ^ 2) := fun a b => by positivity
  calc 1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2)
      ≤ ∑ b ∈ univ.filter (fun b => i < b), 1 / Real.sqrt (∑ k, (x i k - x b k) ^ 2) :=
        single_le_sum (f := fun b => 1 / Real.sqrt (∑ k, (x i k - x b k) ^ 2)) (fun b _ => hnn i b)
          (mem_filter.mpr ⟨mem_univ j, hij⟩)
    _ ≤ ∑ a, ∑ b ∈ univ.filter (fun b => a < b), 1 / Real.sqrt (∑ k, (x a k - x b k) ^ 2) :=
        single_le_sum (f := fun a => ∑ b ∈ univ.filter (fun b => a < b), 1 / Real.sqrt (∑ k, (x a k - x b k) ^ 2))
          (fun a _ => sum_nonneg fun b _ => hnn a b) (mem_univ i)

/-- The points of a configuration of distinct points with energy at most `B` have pairwise squared distances at
least `1/B²`. -/
theorem sep_of_energy_le {B : ℝ} (hB : 0 < B) (x : Fin 11 → Fin 3 → ℝ) (hx : Function.Injective x)
    (hE : energy x ≤ B) : ∀ i j, i ≠ j → 1 / B ^ 2 ≤ ∑ k, (x i k - x j k) ^ 2 := by
  have key : ∀ a b : Fin 11, a < b → 1 / B ^ 2 ≤ ∑ k, (x a k - x b k) ^ 2 := by
    intro a b hab
    have hpos : 0 < ∑ k, (x a k - x b k) ^ 2 := by
      by_contra hle'
      have hle := not_lt.mp hle'
      have h0 : ∑ k, (x a k - x b k) ^ 2 = 0 := le_antisymm hle (sum_nonneg fun k _ => sq_nonneg _)
      have hxab : x a = x b := by
        funext k
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (x a k - x b k))).mp h0 k (mem_univ k)
        have h2 : x a k - x b k = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
        linarith
      exact (ne_of_lt hab) (hx hxab)
    have ht := le_trans (term_le_energy x hab) hE
    have hs : 0 < Real.sqrt (∑ k, (x a k - x b k) ^ 2) := Real.sqrt_pos.mpr hpos
    rw [div_le_iff₀ hs] at ht
    have hsq := Real.sq_sqrt hpos.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (B * Real.sqrt (∑ k, (x a k - x b k) ^ 2) - 1)]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · have h2 := key j i h
    have e : ∑ k, (x j k - x i k) ^ 2 = ∑ k, (x i k - x j k) ^ 2 := sum_congr rfl fun k _ => by ring
    rw [e] at h2
    exact h2

/-- **A minimizer of the energy exists.** -/
theorem exists_minimizer {B : ℝ} (hB : 0 < B) {x0 : Fin 11 → Fin 3 → ℝ} (h0 : OnSphere x0)
    (hi0 : Function.Injective x0) (hE0 : energy x0 ≤ B) :
    ∃ X : Fin 11 → Fin 3 → ℝ, OnSphere X ∧ Function.Injective X ∧ energy X ≤ B ∧
      ∀ x : Fin 11 → Fin 3 → ℝ, OnSphere x → Function.Injective x → energy X ≤ energy x := by
  have hδ : (0 : ℝ) < 1 / B ^ 2 := by positivity
  have hx0 : x0 ∈ Kset (1 / B ^ 2) := ⟨h0, sep_of_energy_le hB x0 hi0 hE0⟩
  obtain ⟨X, hX, hmin⟩ := (isCompact_Kset (1 / B ^ 2)).exists_isMinOn ⟨x0, hx0⟩ (continuousOn_energy hδ)
  have hmin' := isMinOn_iff.mp hmin
  have hXinj : Function.Injective X := by
    intro i j hij
    by_contra hne
    have h1 := hX.2 i j hne
    rw [hij] at h1
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero] at h1
    linarith
  have hXB : energy X ≤ B := le_trans (hmin' x0 hx0) hE0
  refine ⟨X, hX.1, hXinj, hXB, fun x hx hinj => ?_⟩
  by_contra hlt'
  have hlt := not_le.mp hlt'
  exact absurd (hmin' x ⟨hx, sep_of_energy_le hB x hinj (le_trans hlt.le hXB)⟩) (not_le.mpr hlt)

end N11.Analytic
