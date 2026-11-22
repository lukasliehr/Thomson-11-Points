module

public import N11.ParallelResearch1.Circ.Cell

/-!
# The linear programming bound on the two-sphere with a slack, from the kernels of the circle

`circ A W k` is the pair `(R k, R (k + 1))` of the kernels of the circle (`R 0 = 1`, `R 1 = A`,
`R (k + 1) = 2 A R k - W R (k - 1)`; `qV2` of `Value.lean`).

A *term* is a weight `wn / wd`, a function `g` and a degree `m`; its value at `(u, v, t)` is
`(wn / wd) g(u) g(v) R_m(t - u v, (1 - u²)(1 - v²))`. For unit vectors `x`, `y` of `ℝ³` with third coordinates `u`, `v`
and inner product `t` this is `(wn / wd) g(u) g(v) Re((z w̄) ^ m)` with `z`, `w` the projections to the plane of the
first two coordinates, a positive semidefinite kernel (`qV2_quad_nonneg`). By the addition theorem every Legendre
polynomial is a sum of such terms.

* `lp_psd`: if `H t - h0` is a sum of terms, as an identity in `u, v, t`, then `∑ i j, (H ⟨x_i, x_j⟩ - h0) ≥ 0` for
  unit vectors.
* `lp_top`: if moreover `H ≤ (2 - 2 t) ^ (-1/2)` on `[-1, T1]`, `H + c ≤ (2 - 2 t) ^ (-1/2)` on `[73/100, T1]`, a pair
  with inner product above `T1` alone has energy above `Et`, and `Et < (N² h0 - N H(1)) / 2 + c`, then every
  configuration of `N` distinct unit vectors with Coulomb energy at most `Et` has all inner products below `73/100`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-- The kernels of the circle: `(R k, R (k + 1))`. -/
def circ (A W : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, A)
  | k + 1 => ((circ A W k).2, 2 * A * (circ A W k).2 - W * (circ A W k).1)

theorem circ_eq (A W : ℝ) : ∀ k, circ A W k = (qV2 A W k, qV2 A W (k + 1))
  | 0 => by
    show ((1 : ℝ), A) = (1, ((cf 0 : ℕ) : ℝ) * A * 1 - W * 0)
    rw [cf_zero]
    simp
  | k + 1 => by
    have ih := circ_eq A W k
    show ((circ A W k).2, 2 * A * (circ A W k).2 - W * (circ A W k).1) = _
    rw [ih]
    show (qV2 A W (k + 1), 2 * A * qV2 A W (k + 1) - W * qV2 A W k)
      = (qV2 A W (k + 1), ((cf (k + 1) : ℕ) : ℝ) * A * (qPair2 A W (k + 1)).2 - W * (qPair2 A W (k + 1)).1)
    rw [cf_succ]
    have e1 : (qPair2 A W (k + 1)).1 = qV2 A W k := rfl
    have e2 : (qPair2 A W (k + 1)).2 = qV2 A W (k + 1) := rfl
    rw [e1, e2]
    norm_num

/-- A term of an expansion in the kernels of the circle. -/
structure LTerm where
  wn : ℕ
  wd : ℕ
  g : ℝ → ℝ
  m : ℕ

/-- The value of a term. -/
noncomputable def LTerm.val (τ : LTerm) (u v t : ℝ) : ℝ :=
  (τ.wn : ℝ) / τ.wd * τ.g u * τ.g v * (circ (t - u * v) ((1 - u ^ 2) * (1 - v ^ 2)) τ.m).1

theorem sum_sum_list {ι : Type*} [Fintype ι] {β : Type*} (l : List β) (f : ι → ι → β → ℝ) :
    ∑ i, ∑ j, (l.map (f i j)).sum = (l.map fun τ => ∑ i, ∑ j, f i j τ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, sum_add_distrib]
    rw [ih]

section Points

variable {N : ℕ} {x : Fin N → EuclideanSpace ℝ (Fin 3)}

theorem inner_coords (y z : EuclideanSpace ℝ (Fin 3)) : inner ℝ y z = y 0 * z 0 + y 1 * z 1 + y 2 * z 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp [mul_comm]

theorem norm_coords {y : EuclideanSpace ℝ (Fin 3)} (h : ‖y‖ = 1) : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1 := by
  have h2 : inner ℝ y y = 1 := by
    rw [real_inner_self_eq_norm_sq, h]
    norm_num
  rw [inner_coords] at h2
  linarith

/-- **The positivity of an expansion in the kernels of the circle.** -/
theorem lp_psd (hx : ∀ i, ‖x i‖ = 1) (H : ℝ → ℝ) (h0 : ℝ) (terms : List LTerm)
    (hid : ∀ u v t : ℝ, H t - h0 = (terms.map fun τ => τ.val u v t).sum) :
    0 ≤ ∑ i, ∑ j, (H (inner ℝ (x i) (x j)) - h0) := by
  have e : ∀ i j, H (inner ℝ (x i) (x j)) - h0
      = (terms.map fun τ => (τ.wn : ℝ) / τ.wd * (τ.g (x i 2) * τ.g (x j 2)
          * qV2 (x i 0 * x j 0 + x i 1 * x j 1) ((x i 0 ^ 2 + x i 1 ^ 2) * (x j 0 ^ 2 + x j 1 ^ 2)) τ.m)).sum := by
    intro i j
    rw [hid (x i 2) (x j 2)]
    congr 1
    refine List.map_congr_left fun τ _ => ?_
    unfold LTerm.val
    have hi := norm_coords (hx i)
    have hj := norm_coords (hx j)
    have eA : inner ℝ (x i) (x j) - x i 2 * x j 2 = x i 0 * x j 0 + x i 1 * x j 1 := by
      rw [inner_coords]
      ring
    have eW : (1 - x i 2 ^ 2) * (1 - x j 2 ^ 2) = (x i 0 ^ 2 + x i 1 ^ 2) * (x j 0 ^ 2 + x j 1 ^ 2) := by
      have e1 : 1 - x i 2 ^ 2 = x i 0 ^ 2 + x i 1 ^ 2 := by linarith
      have e2 : 1 - x j 2 ^ 2 = x j 0 ^ 2 + x j 1 ^ 2 := by linarith
      rw [e1, e2]
    rw [eA, eW, circ_eq]
    ring
  simp only [e]
  rw [sum_sum_list]
  refine List.sum_nonneg ?_
  intro y hy
  obtain ⟨τ, _, rfl⟩ := List.mem_map.mp hy
  have hq := qV2_quad_nonneg τ.m (fun i => τ.g (x i 2)) (fun i => x i 0) (fun i => x i 1)
  have hw : (0 : ℝ) ≤ (τ.wn : ℝ) / τ.wd := by positivity
  have : ∑ i, ∑ j, (τ.wn : ℝ) / τ.wd * (τ.g (x i 2) * τ.g (x j 2)
      * qV2 (x i 0 * x j 0 + x i 1 * x j 1) ((x i 0 ^ 2 + x i 1 ^ 2) * (x j 0 ^ 2 + x j 1 ^ 2)) τ.m)
      = (τ.wn : ℝ) / τ.wd * ∑ i, ∑ j, τ.g (x i 2) * τ.g (x j 2)
        * qV2 (x i 0 * x j 0 + x i 1 * x j 1) ((x i 0 ^ 2 + x i 1 ^ 2) * (x j 0 ^ 2 + x j 1 ^ 2)) τ.m := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
  rw [this]
  exact mul_nonneg hw hq

/-- **The linear programming bound with a slack: the inner products of a configuration of small energy are below
`73/100`.** -/
theorem lp_top (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x) {H : ℝ → ℝ} {h0 c T1 Et : ℝ}
    (hpsd : 0 ≤ ∑ i, ∑ j, (H (inner ℝ (x i) (x j)) - h0))
    (hS1 : ∀ t, -1 ≤ t → t ≤ T1 → H t ≤ 1 / Real.sqrt (2 - 2 * t))
    (hS2 : ∀ t, 73 / 100 ≤ t → t ≤ T1 → H t + c ≤ 1 / Real.sqrt (2 - 2 * t))
    (hT1 : T1 < 1) (hfT : Et < 1 / Real.sqrt (2 - 2 * T1))
    (hbud : Et < ((N : ℝ) ^ 2 * h0 - N * H 1) / 2 + c) (hE : energy x ≤ Et) :
    ∀ i j, i ≠ j → inner ℝ (x i) (x j) < 73 / 100 := by
  -- the terms of the energy
  have hpos : ∀ i j : Fin N, i ≠ j → 0 < ‖x i - x j‖ := fun i j hij =>
    norm_pos_iff.mpr (sub_ne_zero.mpr fun e => hij (hinj e))
  have hterm : ∀ i j : Fin N, i < j → 1 / ‖x i - x j‖ ≤ energy x := by
    intro i j hij
    unfold energy
    have h1 : 1 / ‖x i - x j‖ ≤ ∑ j' ∈ univ.filter (fun j' => i < j'), 1 / ‖x i - x j'‖ :=
      single_le_sum (f := fun j' => 1 / ‖x i - x j'‖) (fun j' _ => by positivity) (mem_filter.mpr ⟨mem_univ j, hij⟩)
    have h2 : ∑ j' ∈ univ.filter (fun j' => i < j'), 1 / ‖x i - x j'‖
        ≤ ∑ i', ∑ j' ∈ univ.filter (fun j' => i' < j'), 1 / ‖x i' - x j'‖ :=
      single_le_sum (f := fun i' => ∑ j' ∈ univ.filter (fun j' => i' < j'), 1 / ‖x i' - x j'‖)
        (fun i' _ => sum_nonneg fun j' _ => by positivity) (mem_univ i)
    exact le_trans h1 h2
  have hlt1 : ∀ i j : Fin N, i ≠ j → inner ℝ (x i) (x j) < 1 := by
    intro i j hij
    have h1 := hpos i j hij
    have h2 : ‖x i - x j‖ ^ 2 = 2 - 2 * inner ℝ (x i) (x j) := by
      rw [@norm_sub_sq_real, hx i, hx j]
      ring
    have h3 : 0 < ‖x i - x j‖ ^ 2 := by positivity
    linarith
  -- every inner product is at most `T1`
  have hT : ∀ i j : Fin N, i < j → inner ℝ (x i) (x j) ≤ T1 := by
    intro i j hij
    by_contra hno
    have hgt : T1 < inner ℝ (x i) (x j) := not_le.mp hno
    have h1 := hlt1 i j hij.ne
    have hs : Real.sqrt (2 - 2 * inner ℝ (x i) (x j)) < Real.sqrt (2 - 2 * T1) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hs0 : 0 < Real.sqrt (2 - 2 * inner ℝ (x i) (x j)) := Real.sqrt_pos.mpr (by linarith)
    have hf : 1 / Real.sqrt (2 - 2 * T1) < 1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j)) :=
      one_div_lt_one_div_of_lt hs0 hs
    have := hterm i j hij
    rw [← one_div_dist (hx i) (hx j)] at this
    linarith
  have hlow : ∀ i j : Fin N, -1 ≤ inner ℝ (x i) (x j) := fun i j => inner_ge_neg_one (hx i) (hx j)
  -- the sum of `H` over the pairs
  have hsym : ∀ i j : Fin N, H (inner ℝ (x i) (x j)) = H (inner ℝ (x j) (x i)) := fun i j => by
    rw [real_inner_comm]
  have hdiag : ∀ i : Fin N, H (inner ℝ (x i) (x i)) = H 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i]
    norm_num
  have hsplit : ∑ i : Fin N, ∑ j : Fin N, H (inner ℝ (x i) (x j))
      = (∑ i : Fin N, ∑ j : Fin N, if i ≠ j then H (inner ℝ (x i) (x j)) else 0) + N * H 1 := by
    have e : ∀ i : Fin N, ∑ j : Fin N, H (inner ℝ (x i) (x j))
        = (∑ j : Fin N, if i ≠ j then H (inner ℝ (x i) (x j)) else 0) + H 1 := by
      intro i
      rw [← hdiag i, ← add_sum_erase univ (fun j => H (inner ℝ (x i) (x j))) (mem_univ i),
        ← add_sum_erase univ (fun j => if i ≠ j then H (inner ℝ (x i) (x j)) else 0) (mem_univ i)]
      have : ∀ j ∈ univ.erase i, (if i ≠ j then H (inner ℝ (x i) (x j)) else 0) = H (inner ℝ (x i) (x j)) :=
        fun j hj => if_pos (ne_of_mem_erase hj).symm
      rw [sum_congr rfl this]
      simp
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib]
    simp
  have hpairs : (∑ i : Fin N, ∑ j : Fin N, if i ≠ j then H (inner ℝ (x i) (x j)) else 0)
      = 2 * ∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), H (inner ℝ (x i) (x j)) :=
    CAP.ThreePoint.sum_ne_eq_two_mul_sum_lt (fun i j => H (inner ℝ (x i) (x j))) hsym
  have hconst : ∑ _i : Fin N, ∑ _j : Fin N, h0 = (N : ℝ) ^ 2 * h0 := by
    simp
    ring
  have hHsum : ((N : ℝ) ^ 2 * h0 - N * H 1) / 2
      ≤ ∑ i : Fin N, ∑ j ∈ univ.filter (fun j => i < j), H (inner ℝ (x i) (x j)) := by
    have h1 : ∑ i : Fin N, ∑ j : Fin N, (H (inner ℝ (x i) (x j)) - h0)
        = (∑ i : Fin N, ∑ j : Fin N, H (inner ℝ (x i) (x j))) - (N : ℝ) ^ 2 * h0 := by
      rw [← hconst, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_sub_distrib]
    rw [h1, hsplit, hpairs] at hpsd
    linarith
  -- the slack of the pairs
  have hslack : ∀ i j : Fin N, i < j → H (inner ℝ (x i) (x j)) ≤ 1 / ‖x i - x j‖ := by
    intro i j hij
    rw [← one_div_dist (hx i) (hx j)]
    exact hS1 _ (hlow i j) (hT i j hij)
  intro a b hab
  by_contra hno
  have hge : 73 / 100 ≤ inner ℝ (x a) (x b) := not_lt.mp hno
  -- a pair `i < j` with inner product at least `73/100`
  obtain ⟨i, j, hij, hge'⟩ : ∃ i j : Fin N, i < j ∧ 73 / 100 ≤ inner ℝ (x i) (x j) := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, hge⟩
    · exact ⟨b, a, h, by rw [real_inner_comm]; exact hge⟩
  have hbig : H (inner ℝ (x i) (x j)) + c ≤ 1 / ‖x i - x j‖ := by
    rw [← one_div_dist (hx i) (hx j)]
    exact hS2 _ hge' (hT i j hij)
  have hEge : (∑ i' : Fin N, ∑ j' ∈ univ.filter (fun j' => i' < j'), H (inner ℝ (x i') (x j'))) + c ≤ energy x := by
    unfold energy
    have hd : ∀ i' : Fin N, ∀ j' ∈ univ.filter (fun j' => i' < j'),
        0 ≤ 1 / ‖x i' - x j'‖ - H (inner ℝ (x i') (x j')) := fun i' j' hj' =>
      sub_nonneg.mpr (hslack i' j' (mem_filter.mp hj').2)
    have h1 : c ≤ ∑ j' ∈ univ.filter (fun j' => i < j'), (1 / ‖x i - x j'‖ - H (inner ℝ (x i) (x j'))) := by
      have := single_le_sum (f := fun j' => 1 / ‖x i - x j'‖ - H (inner ℝ (x i) (x j'))) (hd i)
        (mem_filter.mpr ⟨mem_univ j, hij⟩)
      linarith
    have h2 : ∑ j' ∈ univ.filter (fun j' => i < j'), (1 / ‖x i - x j'‖ - H (inner ℝ (x i) (x j')))
        ≤ ∑ i' : Fin N, ∑ j' ∈ univ.filter (fun j' => i' < j'), (1 / ‖x i' - x j'‖ - H (inner ℝ (x i') (x j'))) :=
      single_le_sum (f := fun i' => ∑ j' ∈ univ.filter (fun j' => i' < j'), (1 / ‖x i' - x j'‖ - H (inner ℝ (x i') (x j'))))
        (fun i' _ => sum_nonneg (hd i')) (mem_univ i)
    have h3 : ∑ i' : Fin N, ∑ j' ∈ univ.filter (fun j' => i' < j'), (1 / ‖x i' - x j'‖ - H (inner ℝ (x i') (x j')))
        = (∑ i' : Fin N, ∑ j' ∈ univ.filter (fun j' => i' < j'), 1 / ‖x i' - x j'‖)
          - ∑ i' : Fin N, ∑ j' ∈ univ.filter (fun j' => i' < j'), H (inner ℝ (x i') (x j')) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i' _ => ?_
      rw [sum_sub_distrib]
    linarith
  linarith

end Points

/-! ## The sign conditions of a packed polynomial with a constant -/

/-- The polynomial with the signed digits of `H` over `2 ^ sP`. -/
noncomputable def packedPoly (wP sP D H : ℕ) (t : ℝ) : ℝ := spolyV wP (1 : ℝ) t D H / 2 ^ sP

/-- The constant `a0p / (2 ^ sP * sc)` of a witness whose polynomial `pen` is constant. -/
theorem penConst_val {S : Sign2} (h1 : S.pen.a0n = 0) (h2 : S.pen.a1p = 0) (h3 : S.pen.a1n = 0) (h4 : S.pen.a2p = 0)
    (h5 : S.pen.a2n = 0) (sP : ℕ) (t : ℝ) :
    S.pen.val (2 ^ sP * (S.sc : ℝ)) t = (S.pen.a0p : ℝ) / (2 ^ sP * (S.sc : ℝ)) := by
  unfold Pen.val
  rw [h1, h2, h3, h4, h5]
  simp

/-- The sign condition of a packed polynomial plus a constant, from the check of the kernel. -/
theorem packed_sign {P : Params} {sP H : ℕ} {I : Ival} {S : Sign2} (hD2 : 2 ≤ P.D) (h : signOk2 P sP H I S = true)
    (h1 : S.pen.a0n = 0) (h2 : S.pen.a1p = 0) (h3 : S.pen.a1n = 0) (h4 : S.pen.a2p = 0) (h5 : S.pen.a2n = 0)
    (t : ℝ) (hlo : I.lo ≤ t) (hhi : t ≤ I.hi) (ht : t < 1) :
    packedPoly P.wP sP P.D H t + (S.pen.a0p : ℝ) / (2 ^ sP * (S.sc : ℝ)) ≤ 1 / Real.sqrt (2 - 2 * t) := by
  have := signOk2_sound hD2 h t hlo hhi ht
  rw [penConst_val h1 h2 h3 h4 h5] at this
  exact this

end N11.Circ
