module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CAP.Wsos.RootedSum
public import CAP.Schema.ThreePoint.Sphere
public import N11.ParallelResearch1.Circ.Value

/-!
# The rooted forms with the kernels of the circle at points

* `qV2_circle`: for two vectors `(a, b)`, `(a', b')` of the plane, the kernel `R k` at `A = a a' + b b'` and
  `W = (a² + b²) (a'² + b'²)` is `Re ((a + i b) ^ k (a' - i b') ^ k)`: the product of the real parts plus the
  product of the imaginary parts of the two powers (`cpow`). Hence the matrix of the kernel at finitely many
  vectors is positive semidefinite for every `k` (`qV2_quad_nonneg`).
* `rootedV2_sum_nonneg`: for finitely many points with coordinates `a1, a2` in the orthogonal complement of the
  root, the sum of the rooted forms over all pairs of points is nonnegative, if the Gram matrices have the
  form `Y Yᵀ` (`CAP.Wsos.GramHolds`).
* `rooted2_root_nonneg`: the same for points of the unit sphere of `ℝ³` and a root on it.
* `rootedV2_symm`, `rootUse2_eq`: the symmetry of a rooted form, and the three rooted forms in which two of the
  three points coincide (`CAP.Wsos.rootUseV`, the polynomial of the share equation).

The statements on values are over an arbitrary commutative ring; only the positivity is over `ℝ`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-! ## The kernels of the circle are positive -/

/-- The real and the imaginary part of `(a + i b) ^ k`. -/
def cpow (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 => (a * (cpow a b k).1 - b * (cpow a b k).2, a * (cpow a b k).2 + b * (cpow a b k).1)

theorem qPair2_circle (a b a' b' : ℝ) : ∀ k : ℕ,
    (qPair2 (a * a' + b * b') ((a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)) (k + 1)).1
        = (cpow a b k).1 * (cpow a' b' k).1 + (cpow a b k).2 * (cpow a' b' k).2
      ∧ (qPair2 (a * a' + b * b') ((a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)) (k + 1)).2
        = (cpow a b (k + 1)).1 * (cpow a' b' (k + 1)).1 + (cpow a b (k + 1)).2 * (cpow a' b' (k + 1)).2
  | 0 => by
    constructor
    · show (1 : ℝ) = _
      simp only [cpow]
      ring
    · show ((cf 0 : ℕ) : ℝ) * (a * a' + b * b') * 1 - (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) * 0 = _
      simp only [cpow, cf_zero]
      push_cast
      ring
  | k + 1 => by
    obtain ⟨h1, h2⟩ := qPair2_circle a b a' b' k
    refine ⟨h2, ?_⟩
    show ((cf (k + 1) : ℕ) : ℝ) * (a * a' + b * b')
          * (qPair2 (a * a' + b * b') ((a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)) (k + 1)).2
        - (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)
          * (qPair2 (a * a' + b * b') ((a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)) (k + 1)).1 = _
    rw [h1, h2, cf_succ]
    simp only [cpow]
    push_cast
    ring

/-- The kernel of the circle at two vectors of the plane. -/
theorem qV2_circle (a b a' b' : ℝ) (k : ℕ) :
    qV2 (a * a' + b * b') ((a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2)) k
      = (cpow a b k).1 * (cpow a' b' k).1 + (cpow a b k).2 * (cpow a' b' k).2 := by
  cases k with
  | zero =>
    show (1 : ℝ) = _
    simp only [cpow]
    ring
  | succ k => exact (qPair2_circle a b a' b' k).2

/-- **The kernels of the circle are positive semidefinite.** -/
theorem qV2_quad_nonneg {ι : Type*} [Fintype ι] (k : ℕ) (α a b : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, α i * α j * qV2 (a i * a j + b i * b j) ((a i ^ 2 + b i ^ 2) * (a j ^ 2 + b j ^ 2)) k := by
  have e : ∑ i, ∑ j, α i * α j * qV2 (a i * a j + b i * b j) ((a i ^ 2 + b i ^ 2) * (a j ^ 2 + b j ^ 2)) k
      = (∑ i, α i * (cpow (a i) (b i) k).1) ^ 2 + (∑ i, α i * (cpow (a i) (b i) k).2) ^ 2 := by
    rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [qV2_circle]
    ring
  rw [e]
  positivity

/-! ## The rooted forms -/

variable {A : Type*} [CommRing A]

/-- The rooted form is symmetric in its two points. -/
theorem rootedV2_symm (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0)) {b c : ℕ} (hb : b < P.q)
    (hc : c < P.q) (E w1 w2 w3 : A) :
    rootedV2 P E w2 w1 w3 ⟨gram, c, b⟩ = rootedV2 P E w1 w2 w3 ⟨gram, b, c⟩ := by
  unfold rootedV2
  refine sum_congr rfl fun κ hκ => ?_
  show qV2 (AhV E w2 w1 w3) (WhV E w2 w1) κ
      * bilV P.wG E w2 w1 (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) c b)
    = qV2 (AhV E w1 w2 w3) (WhV E w1 w2) κ
      * bilV P.wG E w1 w2 (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) b c)
  have hκ' := hG κ (mem_range.mp hκ)
  rw [bilV_gram P hκ' hc hb, bilV_gram P hκ' hb hc, show AhV E w2 w1 w3 = AhV E w1 w2 w3 from by unfold AhV; ring,
    show WhV E w2 w1 = WhV E w1 w2 from by unfold WhV; ring]
  have e : (fun y => featV P.rb E w2 (P.d - κ) c y * featV P.rb E w1 (P.d - κ) b y)
      = fun y => featV P.rb E w1 (P.d - κ) b y * featV P.rb E w2 (P.d - κ) c y := funext fun y => mul_comm _ _
  rw [e]

/-- **The rooted forms of one root are positive.** The points have the classes `cl j`, the variables `w j` with
respect to the root and the coordinates `a1 j, a2 j` in the orthogonal complement of the root; `w3 j k` is the
variable of the pair of the points `j` and `k`. -/
theorem rootedV2_sum_nonneg (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0))
    {ι : Type*} [Fintype ι] (cl : ι → ℕ) (hcl : ∀ j, cl j < P.q) (E : ℝ) (w : ι → ℝ) (w3 : ι → ι → ℝ)
    (a1 a2 : ι → ℝ)
    (hA : ∀ j k, AhV E (w j) (w k) (w3 j k) = a1 j * a1 k + a2 j * a2 k)
    (hW : ∀ j, E ^ 2 - w j ^ 2 = a1 j ^ 2 + a2 j ^ 2) :
    0 ≤ ∑ j, ∑ k, rootedV2 P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩ := by
  have step : ∀ j k, rootedV2 P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩
      = ∑ κ ∈ range gram.length,
          ((cols κ).map fun y => featV P.rb E (w j) (P.d - κ) (cl j) y * featV P.rb E (w k) (P.d - κ) (cl k) y
              * qV2 (a1 j * a1 k + a2 j * a2 k) ((a1 j ^ 2 + a2 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2)) κ).sum := by
    intro j k
    unfold rootedV2
    refine sum_congr rfl fun κ hκ => ?_
    show qV2 (AhV E (w j) (w k) (w3 j k)) (WhV E (w j) (w k)) κ
      * bilV P.wG E (w j) (w k) (P.d - κ) (P.q * (P.d - κ + 1)) (blockOf P (gram.getD κ 0) (P.d - κ) (cl j) (cl k)) = _
    rw [bilV_gram P (hG κ (mem_range.mp hκ)) (hcl j) (hcl k), hA,
      show WhV E (w j) (w k) = (a1 j ^ 2 + a2 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2) from by
        unfold WhV; rw [hW j, hW k],
      mul_comm (qV2 _ _ κ), ← List.sum_map_mul_right]
  have e : ∑ j, ∑ k, rootedV2 P E (w j) (w k) (w3 j k) ⟨gram, cl j, cl k⟩
      = ∑ κ ∈ range gram.length,
          ((cols κ).map fun y => ∑ j, ∑ k,
              featV P.rb E (w j) (P.d - κ) (cl j) y * featV P.rb E (w k) (P.d - κ) (cl k) y
                * qV2 (a1 j * a1 k + a2 j * a2 k) ((a1 j ^ 2 + a2 j ^ 2) * (a1 k ^ 2 + a2 k ^ 2)) κ).sum := by
    simp only [step]
    rw [sum_congr rfl fun j _ => sum_comm, sum_comm]
    refine sum_congr rfl fun κ _ => ?_
    simp only [sum_list_map_comm]
  rw [e]
  refine sum_nonneg fun κ _ => List.sum_nonneg ?_
  intro v hv
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
  exact qV2_quad_nonneg κ (fun j => featV P.rb E (w j) (P.d - κ) (cl j) y) a1 a2

/-- **The rooted forms of a root on the sphere are positive.** -/
theorem rooted2_root_nonneg (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0))
    {ι : Type*} [Fintype ι] (cl : ι → ℕ) (hcl : ∀ j, cl j < P.q)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (hx : ∀ j, ‖x j‖ = 1) (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ = 1)
    (E : ℝ) :
    0 ≤ ∑ j, ∑ k, rootedV2 P E (E * inner ℝ r (x j)) (E * inner ℝ r (x k)) (E * inner ℝ (x j) (x k))
      ⟨gram, cl j, cl k⟩ := by
  obtain ⟨p, q, h⟩ := CAP.ThreePoint.frame_coords r hr
  refine rootedV2_sum_nonneg P gram cols hG cl hcl E (fun j => E * inner ℝ r (x j))
    (fun j k => E * inner ℝ (x j) (x k)) (fun j => E * p (x j)) (fun j => E * q (x j)) ?_ ?_
  · intro j k
    unfold AhV
    rw [h (x j) (x k)]
    ring
  · intro j
    have e := h (x j) (x j)
    rw [real_inner_self_eq_norm_sq, hx j, one_pow] at e
    linear_combination E ^ 2 * e

/-! ## Points that coincide -/

theorem qV2_zero_zero (k : ℕ) : qV2 (0 : A) 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [qV2, qPair2]
  | succ k => simp [qV2, qPair2]

theorem qPair2_sq (a : A) : ∀ k : ℕ, (qPair2 a (a ^ 2) (k + 1)).1 = a ^ k ∧ (qPair2 a (a ^ 2) (k + 1)).2 = a ^ (k + 1)
  | 0 => by
    constructor
    · show (1 : A) = a ^ 0
      rw [pow_zero]
    · show ((cf 0 : ℕ) : A) * a * 1 - a ^ 2 * 0 = a ^ (0 + 1)
      rw [cf_zero]
      push_cast
      ring
  | k + 1 => by
    obtain ⟨h1, h2⟩ := qPair2_sq a k
    refine ⟨h2, ?_⟩
    show ((cf (k + 1) : ℕ) : A) * a * (qPair2 a (a ^ 2) (k + 1)).2 - a ^ 2 * (qPair2 a (a ^ 2) (k + 1)).1 = _
    rw [h1, h2, cf_succ]
    push_cast
    ring

/-- For `W = A ^ 2` the kernel is `A ^ k`. -/
theorem qV2_sq (a : A) (k : ℕ) : qV2 a (a ^ 2) k = a ^ k := by
  cases k with
  | zero =>
    show (1 : A) = a ^ 0
    rw [pow_zero]
  | succ k => exact (qPair2_sq a k).2

/-- The first point is the root: only the kernel of the degree `0` remains. -/
theorem rootedV2_root_first (P : Params) (R : Rooted) (hR : 1 ≤ R.gram.length) (E w : A) :
    rootedV2 P E E w w R
      = E ^ P.d * linV P.wG E w P.d (P.q * (P.d + 1)) (blockOf P (R.gram.getD 0 0) P.d R.b R.c) := by
  unfold rootedV2
  have hA : AhV E E w w = 0 := by unfold AhV; ring
  have hW : WhV E E w = 0 := by unfold WhV; ring
  rw [hA, hW, sum_eq_single_of_mem 0 (mem_range.mpr hR)]
  · rw [qV2_zero_zero, if_pos rfl, one_mul, Nat.sub_zero, bilV_left_E]
  · intro κ _ hκ
    rw [qV2_zero_zero, if_neg hκ, zero_mul]

/-- The two points coincide: the kernels are powers of `E ^ 2 - w ^ 2`. -/
theorem rootedV2_equal_points (P : Params) (R : Rooted) (E w : A) :
    rootedV2 P E w w E R = ∑ k ∈ range R.gram.length, (E ^ 2 - w ^ 2) ^ k
      * bilV P.wG E w w (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c) := by
  unfold rootedV2
  refine sum_congr rfl fun κ _ => ?_
  have hA : AhV E w w E = E ^ 2 - w ^ 2 := by unfold AhV; ring
  have hW : WhV E w w = (E ^ 2 - w ^ 2) ^ 2 := by unfold WhV; ring
  rw [hA, hW, qV2_sq]

/-- **The rooted forms of the share equation.** For a root with the index class `a` and a second point of the
class `b`, the rooted forms at the pairs (root, point), (point, root) and (point, point) add up to
`CAP.Wsos.rootUseV`. -/
theorem rootUse2_eq (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0)) (h1 : 1 ≤ gram.length)
    {a b : ℕ} (ha : a < P.q) (hb : b < P.q) (E w : A) :
    rootedV2 P E E w w ⟨gram, a, b⟩ + rootedV2 P E w E w ⟨gram, b, a⟩ + rootedV2 P E w w E ⟨gram, b, b⟩
      = rootUseV P E w ⟨gram, a, b⟩ := by
  rw [rootedV2_symm P gram cols hG ha hb E E w w, rootedV2_root_first P ⟨gram, a, b⟩ h1,
    rootedV2_equal_points P ⟨gram, b, b⟩]
  unfold rootUseV
  ring

end N11.Circ
