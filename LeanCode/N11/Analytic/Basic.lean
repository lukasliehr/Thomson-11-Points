module

public import N11.Statement
public import N11.Local.Forms
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.IntervalCases

/-!
# The theorem for 11 points, analytic part: configurations, sums over pairs, invariance (row A1)

The statement (`N11/Statement.lean`) uses configurations `x : Fin 11 → Fin 3 → ℝ`. The statement G7 of route G
(`N11/Local/Forms.lean`) uses functions `p : ℕ → ℕ → ℝ` (the point `i < 11`, the coordinate `k < 3`), the inner
product `dot` over `range 3` and the sum `sumP` over the pairs `i < j < 11`. This file relates the two forms and
collects the lemmas on sums over pairs that the analytic part uses.

* `toN`, `ofN`: the two forms of a configuration; `dot_toN`, `energy_eq_En`: the energy of a configuration of the
  sphere is `En (toN x) = sumP (fpot ∘ dot)`, with the potential `fpot t = (2 - 2 t)^(-1/2)` of the inner product;
* `sumP_add`, `sumP_le`, `sumP_rows`, `sumP_lin`, `sum_sq_eq_sumP`: sums over the pairs;
* `dot_sq_le`, `two_mul_abs_dot_le`: the inequality of Cauchy and Schwarz in `ℝ³`;
* `energy_mulVec`, `energy_comp_perm`: the energy does not change under orthogonal maps and relabellings.
-/

@[expose] public section

namespace N11.Analytic

open Finset Matrix N11.Local

/-! ## The two forms of a configuration -/

/-- A configuration of the statement in the form of `N11/Local`. -/
noncomputable def toN (x : Fin 11 → Fin 3 → ℝ) : ℕ → ℕ → ℝ := fun i k =>
  if h : i < 11 then (if h' : k < 3 then x ⟨i, h⟩ ⟨k, h'⟩ else 0) else 0

theorem toN_apply (x : Fin 11 → Fin 3 → ℝ) (i : Fin 11) (k : Fin 3) : toN x i k = x i k := by
  unfold toN
  rw [dif_pos i.isLt, dif_pos k.isLt]

/-- A configuration in the form of `N11/Local` as a configuration of the statement. -/
def ofN (z : ℕ → ℕ → ℝ) : Fin 11 → Fin 3 → ℝ := fun i k => z i k

theorem ofN_toN (x : Fin 11 → Fin 3 → ℝ) : ofN (toN x) = x :=
  funext fun i => funext fun k => toN_apply x i k

theorem toN_ofN (z : ℕ → ℕ → ℝ) {i k : ℕ} (hi : i < 11) (hk : k < 3) : toN (ofN z) i k = z i k := by
  unfold toN ofN
  rw [dif_pos hi, dif_pos hk]

theorem sum_fin11 (f : ℕ → ℝ) : ∑ i : Fin 11, f i = ∑ i ∈ range 11, f i := Fin.sum_univ_eq_sum_range f 11

theorem sum_fin3 (f : ℕ → ℝ) : ∑ k : Fin 3, f k = ∑ k ∈ range 3, f k := Fin.sum_univ_eq_sum_range f 3

/-- Two vectors that agree in the coordinates below `3` have the same inner products. -/
theorem dot_congr {u u' w w' : ℕ → ℝ} (hu : ∀ k, k < 3 → u k = u' k) (hw : ∀ k, k < 3 → w k = w' k) :
    dot u w = dot u' w' := by
  unfold dot
  exact sum_congr rfl fun k hk => by rw [hu k (mem_range.mp hk), hw k (mem_range.mp hk)]

theorem dot_toN (x : Fin 11 → Fin 3 → ℝ) (i j : Fin 11) :
    dot (toN x i) (toN x j) = ∑ k : Fin 3, x i k * x j k := by
  unfold dot
  rw [← sum_fin3 (fun c => toN x i c * toN x j c)]
  exact sum_congr rfl fun k _ => by rw [toN_apply, toN_apply]

theorem dot_ofN (z : ℕ → ℕ → ℝ) (i j : Fin 11) : ∑ k : Fin 3, ofN z i k * ofN z j k = dot (z i) (z j) := by
  unfold dot ofN
  exact sum_fin3 (fun c => z i c * z j c)

/-- A configuration of the statement lies on the sphere iff the inner products of its points with themselves are
`1`. -/
theorem onSphere_iff_dot (x : Fin 11 → Fin 3 → ℝ) : OnSphere x ↔ ∀ i, i < 11 → dot (toN x i) (toN x i) = 1 := by
  unfold OnSphere
  constructor
  · intro h i hi
    have e := dot_toN x ⟨i, hi⟩ ⟨i, hi⟩
    rw [e, ← h ⟨i, hi⟩]
    exact sum_congr rfl fun k _ => by ring
  · intro h i
    have e := dot_toN x i i
    rw [h i i.isLt] at e
    rw [e]
    exact sum_congr rfl fun k _ => by ring

/-! ## The potential and the energy -/

/-- The Coulomb potential of two points of the unit sphere with the inner product `t`. -/
noncomputable def fpot (t : ℝ) : ℝ := 1 / Real.sqrt (2 - 2 * t)

/-- The energy of a configuration in the form of `N11/Local`, from the inner products of its points. -/
noncomputable def En (z : ℕ → ℕ → ℝ) : ℝ := sumP fun i j => fpot (dot (z i) (z j))

theorem sumP_eq_fin (G : ℕ → ℕ → ℝ) :
    ∑ i : Fin 11, ∑ j ∈ univ.filter (fun j : Fin 11 => i < j), G i j = sumP G := by
  unfold sumP
  rw [← sum_fin11 (fun i => ∑ j ∈ range 11, if i < j then G i j else 0)]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, ← sum_fin11 (fun j => if (i : ℕ) < j then G i j else 0)]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : i < j
  · rw [if_pos h, if_pos (show (i : ℕ) < j from h)]
  · rw [if_neg h, if_neg (show ¬ (i : ℕ) < j from h)]

theorem sqdist_eq (x : Fin 11 → Fin 3 → ℝ) (i j : Fin 11) :
    ∑ k, (x i k - x j k) ^ 2 = ∑ k, x i k ^ 2 + ∑ k, x j k ^ 2 - 2 * ∑ k, x i k * x j k := by
  simp only [Fin.sum_univ_three]
  ring

/-- **The energy of a configuration of the sphere from the inner products.** -/
theorem energy_eq_En (x : Fin 11 → Fin 3 → ℝ) (hx : OnSphere x) : energy x = En (toN x) := by
  unfold energy En
  rw [← sumP_eq_fin]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [dot_toN]
  unfold fpot
  rw [sqdist_eq, hx i, hx j]
  ring_nf

/-- The energy depends only on the coordinates below `11` and `3`. -/
theorem En_congr {z z' : ℕ → ℕ → ℝ} (h : ∀ i k, i < 11 → k < 3 → z i k = z' i k) : En z = En z' := by
  unfold En
  refine sumP_congr fun i j hij hj => ?_
  rw [dot_congr (fun k hk => h i k (by omega) hk) (fun k hk => h j k hj hk)]

theorem energy_ofN (z : ℕ → ℕ → ℝ) (hz : OnSphere (ofN z)) : energy (ofN z) = En z := by
  rw [energy_eq_En _ hz]
  exact En_congr fun i k hi hk => toN_ofN z hi hk

/-! ## Vectors -/

theorem dot_sq_le (u w : ℕ → ℝ) : dot u w ^ 2 ≤ dot u u * dot w w := by
  rw [dot_eq, dot_eq, dot_eq]
  nlinarith [sq_nonneg (u 0 * w 1 - u 1 * w 0), sq_nonneg (u 0 * w 2 - u 2 * w 0),
    sq_nonneg (u 1 * w 2 - u 2 * w 1)]

theorem two_mul_abs_dot_le (u w : ℕ → ℝ) : 2 * |dot u w| ≤ dot u u + dot w w := by
  rw [dot_eq, dot_eq, dot_eq]
  rcases abs_cases (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    nlinarith [sq_nonneg (u 0 - w 0), sq_nonneg (u 1 - w 1), sq_nonneg (u 2 - w 2)]
  · rw [h]
    nlinarith [sq_nonneg (u 0 + w 0), sq_nonneg (u 1 + w 1), sq_nonneg (u 2 + w 2)]

theorem dot_self_eq (u : ℕ → ℝ) : dot u u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [dot_eq]
  ring

theorem sq_le_dot_self (u : ℕ → ℝ) {k : ℕ} (hk : k < 3) : u k ^ 2 ≤ dot u u := by
  rw [dot_self_eq]
  interval_cases k <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

/-! ## Sums over the pairs -/

theorem sumP_add (F G : ℕ → ℕ → ℝ) : sumP (fun i j => F i j + G i j) = sumP F + sumP G := by
  unfold sumP
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : i < j
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

theorem sumP_sub (F G : ℕ → ℕ → ℝ) : sumP (fun i j => F i j - G i j) = sumP F - sumP G := by
  have h := sumP_add (fun i j => F i j - G i j) G
  simp only [sub_add_cancel] at h
  linarith

theorem sumP_neg (F : ℕ → ℕ → ℝ) : sumP (fun i j => -F i j) = -sumP F := by
  have h := sumP_mul (-1) F
  simp only [neg_one_mul] at h
  exact h

theorem sumP_le {F G : ℕ → ℕ → ℝ} (h : ∀ i j, i < j → j < 11 → F i j ≤ G i j) : sumP F ≤ sumP G := by
  unfold sumP
  refine sum_le_sum fun i _ => sum_le_sum fun j hj => ?_
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]
    exact h i j hij (mem_range.mp hj)
  · rw [if_neg hij, if_neg hij]

theorem sumP_nonneg {F : ℕ → ℕ → ℝ} (h : ∀ i j, i < j → j < 11 → 0 ≤ F i j) : 0 ≤ sumP F := by
  have := sumP_le (F := fun _ _ => 0) (G := F) h
  unfold sumP at this ⊢
  simpa using this

theorem sumP_const (s : ℝ) : sumP (fun _ _ => s) = 55 * s := by
  unfold sumP
  simp only [sum_range_succ, sum_range_zero]
  norm_num
  ring

/-- `sumP` of a function that vanishes on the pairs `i < j` is `0`. -/
theorem sumP_eq_zero {F : ℕ → ℕ → ℝ} (h : ∀ i j, i < j → j < 11 → F i j = 0) : sumP F = 0 := by
  have h1 := sumP_le (F := F) (G := fun _ _ => 0) fun i j hij hj => le_of_eq (h i j hij hj)
  have h2 := sumP_le (F := fun _ _ => 0) (G := F) fun i j hij hj => le_of_eq (h i j hij hj).symm
  rw [sumP_const, mul_zero] at h1 h2
  linarith

/-- The sum of a symmetric function over all ordered pairs. -/
theorem sum_sq_eq_sumP (G : ℕ → ℕ → ℝ) (hsym : ∀ i j, i < 11 → j < 11 → G i j = G j i) :
    ∑ i ∈ range 11, ∑ j ∈ range 11, G i j = 2 * sumP G + ∑ i ∈ range 11, G i i := by
  have split : ∀ i, ∑ j ∈ range 11, G i j
      = (∑ j ∈ range 11, if i < j then G i j else 0) + (∑ j ∈ range 11, if j < i then G i j else 0)
        + ∑ j ∈ range 11, if j = i then G i j else 0 := by
    intro i
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h)]
      ring
    · subst h
      simp
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (ne_of_lt h)]
      ring
  have hdiag : ∀ i, i < 11 → (∑ j ∈ range 11, if j = i then G i j else 0) = G i i := by
    intro i hi
    rw [Finset.sum_ite_eq' (range 11) i (fun j => G i j), if_pos (mem_range.mpr hi)]
  have hswap : ∑ i ∈ range 11, ∑ j ∈ range 11, (if j < i then G i j else 0)
      = ∑ i ∈ range 11, ∑ j ∈ range 11, (if i < j then G i j else 0) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h, hsym j i (mem_range.mp hj) (mem_range.mp hi)]
    · rw [if_neg h, if_neg h]
  rw [sum_congr rfl fun i _ => split i, sum_add_distrib, sum_add_distrib, hswap,
    sum_congr rfl fun i hi => hdiag i (mem_range.mp hi)]
  unfold sumP
  ring

/-- **A sum over the pairs of a symmetric weight times the sum of two values of the points.** -/
theorem sumP_rows (w : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (hw : ∀ i j, i < j → j < 11 → w i j = w j i) :
    sumP (fun i j => w i j * (φ i + φ j)) = ∑ i ∈ range 11, φ i * rowS w i := by
  -- the second half, with the names of the points exchanged
  have h2 : (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * φ j else 0)
      = ∑ i ∈ range 11, ∑ j ∈ range 11, if j < i then w i j * φ i else 0 := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    by_cases h : j < i
    · rw [if_pos h, if_pos h, hw j i h (mem_range.mp hi)]
    · rw [if_neg h, if_neg h]
  have e : sumP (fun i j => w i j * (φ i + φ j))
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * φ i else 0)
        + ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * φ j else 0 := by
    unfold sumP
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  rw [e, h2, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold rowS
  rw [← sum_add_distrib, Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h)]
    ring
  · subst h
    simp
  · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (ne_of_lt h)]
    ring

/-- The inner product with a sum of vectors. -/
theorem dot_sum_left (s : Finset ℕ) (f : ℕ → ℕ → ℝ) (w : ℕ → ℝ) :
    dot (fun k => ∑ i ∈ s, f i k) w = ∑ i ∈ s, dot (f i) w := by
  unfold dot
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]

/-- **The first-order term of a sum over the pairs with a symmetric weight.** With `frc z w i = ∑_{j ≠ i} w_ij z_j`:
`∑_{i<j} w_ij (<z_i, e_j> + <e_i, z_j>) = ∑_i <frc z w i, e_i>`. -/
theorem sumP_lin (w z e : ℕ → ℕ → ℝ) (hw : ∀ i j, i < j → j < 11 → w i j = w j i) :
    sumP (fun i j => w i j * Lf z e i j) = ∑ i ∈ range 11, dot (frc z w i) (e i) := by
  have hfrc : ∀ i, dot (frc z w i) (e i) = ∑ j ∈ range 11, if j = i then 0 else w i j * dot (z j) (e i) := by
    intro i
    have e1 : frc z w i = fun k => ∑ j ∈ range 11, (fun j k => if j = i then 0 else w i j * z j k) j k := by
      funext k
      unfold frc
      rfl
    rw [e1, dot_sum_left]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : j = i
    · rw [if_pos h]
      unfold dot
      simp only [if_pos h, zero_mul, sum_const_zero]
    · rw [if_neg h]
      unfold dot
      simp only [if_neg h]
      rw [Finset.mul_sum]
      exact sum_congr rfl fun k _ => by ring
  have hsplit : sumP (fun i j => w i j * Lf z e i j)
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * dot (z i) (e j) else 0)
        + ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * dot (e i) (z j) else 0 := by
    unfold sumP Lf
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  -- the pairs `j < i` of the sum of the right side
  have hA : (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * dot (z i) (e j) else 0)
      = ∑ i ∈ range 11, ∑ j ∈ range 11, if j < i then w i j * dot (z j) (e i) else 0 := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    by_cases h : j < i
    · rw [if_pos h, if_pos h, hw j i h (mem_range.mp hi)]
    · rw [if_neg h, if_neg h]
  -- the pairs `i < j` of the sum of the right side
  have hB : (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * dot (e i) (z j) else 0)
      = ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then w i j * dot (z j) (e i) else 0 :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [dot_comm (e i) (z j)]
  rw [hsplit, hA, hB, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [hfrc, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (ne_of_gt h)]
    ring
  · subst h
    simp
  · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg (ne_of_lt h)]
    ring

/-! ## Orthogonal maps and relabellings -/

/-- An orthogonal map preserves the inner product. -/
theorem dot_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (v w : Fin 3 → ℝ) : ∑ c, U.mulVec v c * U.mulVec w c = ∑ c, v c * w c := by
  have h1 : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU
  have h2 : dotProduct (U.mulVec v) (U.mulVec w) = dotProduct v w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact h2

/-- An orthogonal map preserves squared distances. -/
theorem sqdist_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (v w : Fin 3 → ℝ) : ∑ k, (U.mulVec v k - U.mulVec w k) ^ 2 = ∑ k, (v k - w k) ^ 2 := by
  have h := dot_mulVec U hU (v - w) (v - w)
  rw [Matrix.mulVec_sub] at h
  have e1 : ∀ k, (U.mulVec v k - U.mulVec w k) ^ 2
      = (U.mulVec v - U.mulVec w) k * (U.mulVec v - U.mulVec w) k := fun k => by
    rw [Pi.sub_apply]
    ring
  have e2 : ∀ k, (v k - w k) ^ 2 = (v - w) k * (v - w) k := fun k => by
    rw [Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_congr rfl fun k _ => e2 k]
  exact h

theorem onSphere_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin 11 → Fin 3 → ℝ) (hx : OnSphere x) : OnSphere (fun i => U.mulVec (x i)) := by
  intro i
  have h := dot_mulVec U hU (x i) (x i)
  have e1 : ∑ k, U.mulVec (x i) k ^ 2 = ∑ k, U.mulVec (x i) k * U.mulVec (x i) k :=
    Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, x i k * x i k = ∑ k, x i k ^ 2 := Finset.sum_congr rfl fun k _ => by ring
  show ∑ k, U.mulVec (x i) k ^ 2 = 1
  rw [e1, h, e2]
  exact hx i

theorem injective_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin 11 → Fin 3 → ℝ) (hx : Function.Injective x) : Function.Injective (fun i => U.mulVec (x i)) := by
  intro i j hij
  have h1 : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU
  apply hx
  have := congrArg (fun v => Uᵀ.mulVec v) hij
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
  exact this

/-- An orthogonal map preserves the energy. -/
theorem energy_mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (x : Fin 11 → Fin 3 → ℝ) : energy (fun i => U.mulVec (x i)) = energy x := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show 1 / Real.sqrt (∑ k, (U.mulVec (x i) k - U.mulVec (x j) k) ^ 2) = _
  rw [sqdist_mulVec U hU]

/-- A symmetric function of two labels that vanishes on the diagonal: the sum over all ordered pairs is twice
the sum over the pairs `i < j`. -/
theorem sum_all_eq {N : ℕ} (F : Fin N → Fin N → ℝ) (hsym : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
  have split : ∀ i : Fin N, ∑ j, F i j
      = ∑ j ∈ univ.filter (fun j => i < j), F i j + ∑ j ∈ univ.filter (fun j => j < i), F i j := by
    intro i
    have h1 := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin N)) (fun j => i < j) (fun j => F i j)
    have hset : univ.filter (fun j => ¬ i < j) = insert i (univ.filter (fun j => j < i)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact le_of_eq h
        · exact le_of_lt h
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ i < j), F i j = ∑ j ∈ univ.filter (fun j => j < i), F i j := by
      rw [hset, Finset.sum_insert (by simp), hd, zero_add]
    rw [← h1, h2]
  have swap : ∑ i, ∑ j ∈ univ.filter (fun j => j < i), F i j
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
    rw [Finset.sum_comm' (s' := fun j => univ.filter (fun i => j < i)) (t' := univ)]
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsym b a
    · intro a b
      simp
  rw [Finset.sum_congr rfl fun i _ => split i, Finset.sum_add_distrib, swap]
  ring

/-- **A sum of a symmetric function over the pairs `i < j` does not depend on the labelling.** -/
theorem pairsum_comp_perm {N : ℕ} (F : Fin N → Fin N → ℝ) (hsym : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F (σ i) (σ j) = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
  have h1 := sum_all_eq F hsym hd
  have h2 := sum_all_eq (fun i j => F (σ i) (σ j)) (fun i j => hsym _ _) (fun i => hd _)
  have h3 : ∑ i, ∑ j, F (σ i) (σ j) = ∑ i, ∑ j, F i j :=
    calc ∑ i, ∑ j, F (σ i) (σ j)
        = ∑ i, ∑ j, F (σ i) j := Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => F (σ i) j)
      _ = ∑ i, ∑ j, F i j := Equiv.sum_comp σ (fun i => ∑ j, F i j)
  linarith

/-- **The energy does not depend on the labelling of the points.** -/
theorem energy_comp_perm (x : Fin 11 → Fin 3 → ℝ) (σ : Equiv.Perm (Fin 11)) :
    energy (fun i => x (σ i)) = energy x := by
  unfold energy
  exact pairsum_comp_perm (fun i j => 1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2))
    (fun i j => by
      have e : ∑ k, (x i k - x j k) ^ 2 = ∑ k, (x j k - x i k) ^ 2 :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [e])
    (fun i => by simp) σ

/-- The energy of the image of a configuration under an orthogonal map and a relabelling. -/
theorem energy_of_congr (x y : Fin 11 → Fin 3 → ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (σ : Equiv.Perm (Fin 11)) (h : ∀ i, y i = U.mulVec (x (σ i))) :
    energy y = energy x := by
  have e : y = fun i => U.mulVec ((fun i => x (σ i)) i) := funext h
  rw [e, energy_mulVec U hU, energy_comp_perm]

end N11.Analytic
