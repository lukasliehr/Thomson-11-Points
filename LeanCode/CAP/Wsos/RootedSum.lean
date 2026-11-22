module

public import CAP.Wsos.Gram
public import CAP.Wsos.Rooted
public import CAP.Wsos.Legendre

/-!
# The rooted forms at points

The rooted form of a root class is `∑ k, (d! / k!) * R k * (the bilinear form of the Gram matrix G k)`.
Let the Gram matrices have the form `Y Yᵀ` (`GramHolds`, the conclusion of `gramOk_sound`).

* `bilV_gram`: the bilinear form of a block of `G` is `∑ columns y, φ y (first point) * φ y (second point)`
  with the feature `φ y` of a point (`featV`).
* `rootedV_sum_nonneg`: for finitely many points with coordinates `a1, a2, a3` in the orthogonal
  complement of the root, the sum of the rooted forms over all pairs of points is nonnegative. This
  combines `bilV_gram` with `qV_quad_nonneg`.
* `rootedV_symm`: the rooted form is symmetric in its two points.
* `rootUse_eq`: the three rooted forms in which two of the three points coincide add up to `d!`
  times the polynomial `rootUseV` of the share equation.

The statements on values are over an arbitrary commutative ring; only the positivity is over `ℝ`.
-/

@[expose] public section

namespace CAP.Wsos

open Finset

variable {A : Type*} [CommRing A]

/-! ## The Gram matrix as a sum over the columns -/

/-- The feature of the column `y` of a rooted block for a point of the class `b` with the variable `w`. -/
def featV (rb : ℕ) (E w : A) (n b y : ℕ) : A :=
  ∑ p ∈ range (n + 1), (sdig rb y (b * (n + 1) + p) : A) * hpow E w n p

theorem list_sum_bil (cols : List ℕ) (n : ℕ) (a c : ℕ → ℕ → ℤ) (h1 h2 : ℕ → A) :
    ∑ j ∈ range (n + 1), h2 j * ∑ i ∈ range (n + 1), (((cols.map fun y => a y i * c y j).sum : ℤ) : A) * h1 i
      = (cols.map fun y => (∑ i ∈ range (n + 1), (a y i : A) * h1 i) * (∑ j ∈ range (n + 1), (c y j : A) * h2 j)).sum := by
  induction cols with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, add_mul, sum_add_distrib, mul_add]
    rw [ih]
    congr 1
    rw [sum_mul_sum, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring

theorem sum_list_map_comm {ι : Type*} (s : Finset ι) (l : List ℕ) (f : ι → ℕ → A) :
    ∑ j ∈ s, (l.map (f j)).sum = (l.map fun y => ∑ j ∈ s, f j y).sum := by
  induction l with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]

theorem sdig_blockOf (P : Params) (G n b c j i : ℕ) :
    sdig P.wG (blockOf P G n b c) (P.q * (n + 1) * j + i)
      = sdig P.wG G ((b * (n + 1) + i) + P.q * (n + 1) * (c * (n + 1) + j)) := by
  show sdig P.wG (G >>> (P.wG * (b * (n + 1) + P.q * (n + 1) * (c * (n + 1))))) _ = _
  rw [sdig_shift]
  congr 1
  ring

theorem block_index_lt {q b n i : ℕ} (hb : b < q) (hi : i < n + 1) : b * (n + 1) + i < q * (n + 1) :=
  calc b * (n + 1) + i < b * (n + 1) + (n + 1) := by omega
    _ = (b + 1) * (n + 1) := by ring
    _ ≤ q * (n + 1) := Nat.mul_le_mul_right _ hb

/-- The bilinear form of a block of a Gram matrix `Y Yᵀ` is a sum of products of features. -/
theorem bilV_gram (P : Params) {n : ℕ} {cols : List ℕ} {G : ℕ} (hG : GramHolds P n cols G) {b c : ℕ}
    (hb : b < P.q) (hc : c < P.q) (E w1 w2 : A) :
    bilV P.wG E w1 w2 n (P.q * (n + 1)) (blockOf P G n b c)
      = (cols.map fun y => featV P.rb E w1 n b y * featV P.rb E w2 n c y).sum := by
  have key : ∀ j ∈ range (n + 1), ∀ i ∈ range (n + 1),
      sdig P.wG (blockOf P G n b c) (P.q * (n + 1) * j + i)
        = (cols.map fun y => sdig P.rb y (b * (n + 1) + i) * sdig P.rb y (c * (n + 1) + j)).sum := by
    intro j hj i hi
    rw [sdig_blockOf, hG _ _ (block_index_lt hb (mem_range.mp hi)) (block_index_lt hc (mem_range.mp hj))]
  unfold bilV featV
  rw [← list_sum_bil cols n (fun y i => sdig P.rb y (b * (n + 1) + i)) (fun y j => sdig P.rb y (c * (n + 1) + j))
    (fun i => hpow E w1 n i) (fun j => hpow E w2 n j)]
  refine sum_congr rfl fun j hj => ?_
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [key j hj i hi]

/-- The rooted form is symmetric in its two points. -/
theorem rootedV_symm (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0)) {b c : ℕ} (hb : b < P.q)
    (hc : c < P.q) (E w1 w2 w3 : A) :
    rootedV P E w2 w1 w3 ⟨gram, c, b⟩ = rootedV P E w1 w2 w3 ⟨gram, b, c⟩ := by
  unfold rootedV
  refine sum_congr rfl fun κ hκ => ?_
  show _ * (qV (AhV E w2 w1 w3) (WhV E w2 w1) κ
      * bilV P.wG E w2 w1 (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) c b))
    = _ * (qV (AhV E w1 w2 w3) (WhV E w1 w2) κ
      * bilV P.wG E w1 w2 (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) b c))
  have hκ' := hG κ (mem_range.mp hκ)
  rw [bilV_gram P hκ' hc hb, bilV_gram P hκ' hb hc, show AhV E w2 w1 w3 = AhV E w1 w2 w3 from by unfold AhV; ring,
    show WhV E w2 w1 = WhV E w1 w2 from by unfold WhV; ring]
  have e : (fun y => featV P.rb E w2 (P.d - κ) c y * featV P.rb E w1 (P.d - κ) b y)
      = fun y => featV P.rb E w1 (P.d - κ) b y * featV P.rb E w2 (P.d - κ) c y := funext fun y => mul_comm _ _
  rw [e]

/-! ## Positivity -/

/-- **The rooted forms of one root are positive.** The points have the classes `cl j`, the variables
`w j` with respect to the root and the coordinates `a1 j, a2 j, a3 j` in the orthogonal complement of
the root; `w3 j k` is the variable of the pair of the points `j` and `k`. -/
theorem rootedV_sum_nonneg (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ) (hlen : gram.length ≤ 9)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0))
    {ι : Type*} [Fintype ι] (cl : ι → ℕ) (hcl : ∀ j, cl j < P.q) (E : ℝ) (w : ι → ℝ) (w3 : ι → ι → ℝ)
    (a1 a2 a3 : ι → ℝ)
    (hA : ∀ j k, AhV E (w j) (w k) (w3 j k) = a1 j * a1 k + a2 j * a2 k + a3 j * a3 k)
    (hW : ∀ j, E ^ 2 - w j ^ 2 = a1 j ^ 2 + a2 j ^ 2 + a3 j ^ 2) :
    0 ≤ ∑ j, ∑ k, rootedV P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩ := by
  have step : ∀ j k, rootedV P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩
      = ∑ κ ∈ range gram.length, (((facts P.d).getD κ 0 : ℕ) : ℝ)
          * ((cols κ).map fun y => featV P.rb E (w j) (P.d - κ) (cl j) y * featV P.rb E (w k) (P.d - κ) (cl k) y
              * qV (a1 j * a1 k + a2 j * a2 k + a3 j * a3 k)
                  ((a1 j ^ 2 + a2 j ^ 2 + a3 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2 + a3 k ^ 2)) κ).sum := by
    intro j k
    unfold rootedV
    refine sum_congr rfl fun κ hκ => ?_
    show _ * (qV (AhV E (w j) (w k) (w3 j k)) (WhV E (w j) (w k)) κ
      * bilV P.wG E (w j) (w k) (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) (cl j) (cl k))) = _
    rw [bilV_gram P (hG κ (mem_range.mp hκ)) (hcl j) (hcl k), hA,
      show WhV E (w j) (w k) = (a1 j ^ 2 + a2 j ^ 2 + a3 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2 + a3 k ^ 2) from by
        unfold WhV; rw [hW j, hW k],
      mul_comm (qV _ _ κ), ← List.sum_map_mul_right]
  have e : ∑ j, ∑ k, rootedV P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩
      = ∑ κ ∈ range gram.length, (((facts P.d).getD κ 0 : ℕ) : ℝ)
          * ((cols κ).map fun y => ∑ j, ∑ k,
              featV P.rb E (w j) (P.d - κ) (cl j) y * featV P.rb E (w k) (P.d - κ) (cl k) y
                * qV (a1 j * a1 k + a2 j * a2 k + a3 j * a3 k)
                    ((a1 j ^ 2 + a2 j ^ 2 + a3 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2 + a3 k ^ 2)) κ).sum := by
    simp only [step]
    rw [sum_congr rfl fun j _ => sum_comm, sum_comm]
    refine sum_congr rfl fun κ _ => ?_
    simp only [← mul_sum]
    congr 1
    simp only [sum_list_map_comm]
  rw [e]
  refine sum_nonneg fun κ hκ => mul_nonneg (Nat.cast_nonneg _) (List.sum_nonneg ?_)
  intro v hv
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
  have hk : κ ≤ 8 := by have := mem_range.mp hκ; omega
  exact qV_quad_nonneg κ hk (fun j => featV P.rb E (w j) (P.d - κ) (cl j) y) a1 a2 a3

/-! ## Points that coincide -/

theorem qV_zero_zero (k : ℕ) : qV (0 : A) 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [qV, qPair]
  | succ k => simp [qV, qPair]

theorem qPair_sq (a : A) : ∀ k : ℕ, (qPair a (a ^ 2) (k + 1)).1 = (k.factorial : A) * a ^ k
    ∧ (qPair a (a ^ 2) (k + 1)).2 = ((k + 1).factorial : A) * a ^ (k + 1)
  | 0 => by simp [qPair]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := qPair_sq a k
    refine ⟨h2, ?_⟩
    show ((2 * (k + 1) + 1 : ℕ) : A) * a * (qPair a (a ^ 2) (k + 1)).2
      - (((k + 1) * (k + 1) : ℕ) : A) * a ^ 2 * (qPair a (a ^ 2) (k + 1)).1 = _
    rw [h1, h2]
    simp only [Nat.factorial_succ]
    push_cast
    ring

/-- For `W = A ^ 2` the kernel is `k! * A ^ k`. -/
theorem qV_sq (a : A) (k : ℕ) : qV a (a ^ 2) k = (k.factorial : A) * a ^ k := by
  cases k with
  | zero => simp [qV, qPair]
  | succ k => exact (qPair_sq a k).2

theorem factsGo_getD (D : ℕ) : ∀ (n g : ℕ) (acc : List ℕ), g * n.factorial = D →
    (∀ i < acc.length, acc.getD i 0 * (n + i).factorial = D) →
    ∀ i < acc.length + n, (factsGo n n g acc).getD i 0 * i.factorial = D
  | 0, g, acc, _, hacc => fun i hi => by
    have h := hacc i (by omega)
    rw [Nat.zero_add] at h
    exact h
  | n + 1, g, acc, hg, hacc => fun i hi => by
    show (factsGo n n (g * (n + 1)) (g * (n + 1) :: acc)).getD i 0 * _ = _
    refine factsGo_getD D n (g * (n + 1)) (g * (n + 1) :: acc) ?_ ?_ i ?_
    · rw [← hg, Nat.factorial_succ]
      ring
    · intro j hj
      cases j with
      | zero =>
        show g * (n + 1) * n.factorial = D
        rw [← hg, Nat.factorial_succ, Nat.mul_assoc]
      | succ j =>
        rw [List.getD_cons_succ, show n + (j + 1) = n + 1 + j by omega]
        exact hacc j (by simpa using hj)
    · rw [List.length_cons]
      omega

/-- The list `facts d` holds the numbers `d! / k!`. -/
theorem facts_getD_mul (d k : ℕ) (hk : k ≤ d) : (facts d).getD k 0 * k.factorial = d.factorial := by
  unfold facts
  refine factsGo_getD d.factorial d 1 [1] (Nat.one_mul _) (fun i hi => ?_) k (by simp; omega)
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  simp

theorem hpow_self (E : A) {n i : ℕ} (hi : i ≤ n) : hpow E E n i = E ^ n := by
  unfold hpow
  rw [← pow_add]
  congr 1
  omega

theorem bilV_left_E (wG : ℕ) (E w : A) (n N Gr : ℕ) : bilV wG E E w n N Gr = E ^ n * linV wG E w n N Gr := by
  unfold bilV linV
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have e : ∑ i ∈ range (n + 1), (sdig wG Gr (N * j + i) : A) * hpow E E n i
      = (∑ i ∈ range (n + 1), (sdig wG Gr (N * j + i) : A)) * E ^ n := by
    rw [sum_mul]
    exact sum_congr rfl fun i hi => by rw [hpow_self E (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  rw [e]
  ring

/-- The first point is the root: only the kernel of the degree `0` remains. -/
theorem rootedV_root_first (P : Params) (R : Rooted) (hR : 1 ≤ R.gram.length) (E w : A) :
    rootedV P E E w w R = (P.d.factorial : A)
      * (E ^ P.d * linV P.wG E w P.d (P.q * (P.d + 1)) (blockOf P (R.gram.getD 0 0) P.d R.b R.c)) := by
  unfold rootedV
  have hA : AhV E E w w = 0 := by unfold AhV; ring
  have hW : WhV E E w = 0 := by unfold WhV; ring
  rw [hA, hW, sum_eq_single_of_mem 0 (mem_range.mpr hR)]
  · have hf := facts_getD_mul P.d 0 (Nat.zero_le _)
    rw [Nat.factorial_zero, Nat.mul_one] at hf
    rw [qV_zero_zero, if_pos rfl, one_mul, Nat.sub_zero, bilV_left_E, hf]
  · intro κ _ hκ
    rw [qV_zero_zero, if_neg hκ, zero_mul, mul_zero]

/-- The two points coincide: the kernels are powers of `E ^ 2 - w ^ 2`. -/
theorem rootedV_equal_points (P : Params) (R : Rooted) (hR : R.gram.length ≤ P.d + 1) (E w : A) :
    rootedV P E w w E R = (P.d.factorial : A) * ∑ k ∈ range R.gram.length, (E ^ 2 - w ^ 2) ^ k
      * bilV P.wG E w w (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c) := by
  unfold rootedV
  rw [mul_sum]
  refine sum_congr rfl fun κ hκ => ?_
  have hA : AhV E w w E = E ^ 2 - w ^ 2 := by unfold AhV; ring
  have hW : WhV E w w = (E ^ 2 - w ^ 2) ^ 2 := by unfold WhV; ring
  have hf := facts_getD_mul P.d κ (by have := mem_range.mp hκ; omega)
  have hf' : (((facts P.d).getD κ 0 : ℕ) : A) * (κ.factorial : A) = (P.d.factorial : A) := by
    rw [← Nat.cast_mul, hf]
  rw [hA, hW, qV_sq, ← hf']
  ring

/-- **The rooted forms of the share equation.** For a root of the class `a` and a second point of the
class `b`, the rooted forms at the pairs (root, point), (point, root) and (point, point) add up to
`d!` times `rootUseV`. -/
theorem rootUse_eq (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0)) (h1 : 1 ≤ gram.length)
    (hlen : gram.length ≤ P.d + 1) {a b : ℕ} (ha : a < P.q) (hb : b < P.q) (E w : A) :
    rootedV P E E w w ⟨gram, a, b⟩ + rootedV P E w E w ⟨gram, b, a⟩ + rootedV P E w w E ⟨gram, b, b⟩
      = (P.d.factorial : A) * rootUseV P E w ⟨gram, a, b⟩ := by
  rw [rootedV_symm P gram cols hG ha hb E E w w, rootedV_root_first P ⟨gram, a, b⟩ h1,
    rootedV_equal_points P ⟨gram, b, b⟩ hlen]
  unfold rootUseV
  ring

end CAP.Wsos
