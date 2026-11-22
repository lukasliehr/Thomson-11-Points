module

public import CAP.Wsos.TypedBound
public import N11.ParallelResearch1.Circ.Sound
public import N11.ParallelResearch1.Circ.RootedSum

/-!
# The typed three-point bound on the unit sphere of `ℝ³`

Let `C` be the data of a typed certificate and `xs` the list of its triple types. The classes of the points are
`0, …, Q - 1`; the class `Q = q - 1` is empty and is the index class of the root in the rooted blocks. Let

* the Gram matrices of the rooted blocks have the form `Y Yᵀ` (`CAP.Wsos.GramHolds`),
* the inequality of every triple type of the list hold (`TyHolds2`, with the kernels of the circle),
* the list contain every triple type that occurs, and the class `last a b` of every pair type be the largest
  class with further points

(`CertHolds2`). Let points `x i` of the unit sphere of `ℝ³` be labelled by classes with the sizes of the
certificate, such that the inner products of all pairs lie in the boxes of their pair types and the generators
of the weights of all triples are nonnegative (`InDomain2`).

`typed_bound2`: then the sum of the constants of the triple types over the triples of points is at most
`3 ∑ i ≠ j, K (x i, x j) + 6 ∑ i, s (x i; root, root)`, where `K` is the pair polynomial of the classes of the
two points and `s` the rooted form. All quantities are in the unit `2 ^ K` of the checker, and the variables are
`2 ^ m` times the inner products (`wv3`).

The proof verifies the three hypotheses of `CAP.Wsos.typed_sum`, as the proof of `CAP.Wsos.typed_bound` does: the
positivity of the rooted forms (`rooted2_root_nonneg`), the share equation and the inequality of the triple
types. In the rooted forms of the root `x i` the point `x i` itself has the index class `Q` (`clq`).
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

open CAP.ThreePoint (Distinct3 distinct3_swap12 distinct3_swap23)

/-! ## Values in the unit `2 ^ K` -/

/-- The share of the pair type `(a, b)` for one point of the class `c`. -/
noncomputable def shareP2 (P : Params) (Q : ℕ) (C : Cert) (a b c : ℕ) (w : ℝ) : ℝ :=
  shareV P ((2 : ℝ) ^ P.m) w (shareOf2 Q C a b c) / ((shareOf2 Q C a b c).mult : ℝ)

/-- The rooted form of a root of the class `a` at points with the index classes `b` and `c`. -/
noncomputable def rootS2 (P : Params) (C : Cert) (a b c : ℕ) (w1 w2 w3 : ℝ) : ℝ :=
  2 ^ P.aF * rootedV2 P ((2 : ℝ) ^ P.m) w1 w2 w3 ⟨C.gram a, b, c⟩

/-- The constant of a triple type. -/
noncomputable def tyC2 (P : Params) (Q : ℕ) (C : Cert) (X : TyX) : ℝ :=
  ((X.c2p : ℝ) - (X.c2n : ℝ))
    / (((shareOf2 Q C X.a X.b X.c).mult : ℝ) * ((shareOf2 Q C X.a X.c X.b).mult : ℝ) * ((shareOf2 Q C X.b X.c X.a).mult : ℝ))

/-! ## The shares of a pair type -/

theorem shareOf2_last (Q : ℕ) (C : Cert) (a b : ℕ) : shareOf2 Q C a b (C.last a b)
    = ⟨mult C a b (C.last a b), C.H a b, tab (C.p a b) (C.last a b), tab (mult C a b) (C.last a b),
        [⟨C.gram a, Q, b⟩, ⟨C.gram b, Q, a⟩]⟩ := by
  unfold shareOf2
  rw [Nat.beq_refl]
  rfl

theorem shareOf2_ne (Q : ℕ) (C : Cert) {a b c : ℕ} (hc : c ≠ C.last a b) : shareOf2 Q C a b c = ⟨1, C.p a b c, [], [], []⟩ := by
  have hb : Nat.beq c (C.last a b) = false := by
    cases hb : Nat.beq c (C.last a b) with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hc
  unfold shareOf2
  rw [hb]
  rfl

theorem shareOf2_mult_pos (Q : ℕ) (C : Cert) {a b c : ℕ} (h : 0 < mult C a b c) : 0 < (shareOf2 Q C a b c).mult := by
  by_cases hc : c = C.last a b
  · rw [hc, shareOf2_last]
    rw [hc] at h
    exact h
  · rw [shareOf2_ne Q C hc]
    exact Nat.one_pos

theorem shareP2_ne (P : Params) (Q : ℕ) (C : Cert) {a b c : ℕ} (hc : c ≠ C.last a b) (w : ℝ) :
    shareP2 P Q C a b c w = 2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b c) := by
  unfold shareP2
  rw [shareOf2_ne Q C hc]
  simp [shareV]

theorem shareV2_last (P : Params) (Q : ℕ) (C : Cert) (a b : ℕ) (w : ℝ) :
    shareV P ((2 : ℝ) ^ P.m) w (shareOf2 Q C a b (C.last a b))
      = 2 ^ P.aP * (spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.H a b)
          - ∑ j ∈ range (C.last a b), (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j))
        - 2 ^ P.aF * (rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, Q, b⟩ + rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram b, Q, a⟩) := by
  have e : ∀ j ∈ range (C.last a b),
      (((tab (mult C a b) (C.last a b)).getD j 0 : ℕ) : ℝ)
          * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D ((tab (C.p a b) (C.last a b)).getD j 0)
        = (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j) :=
    fun j hj => by rw [tab_getD _ (mem_range.mp hj), tab_getD _ (mem_range.mp hj)]
  rw [shareOf2_last]
  unfold shareV
  dsimp only
  rw [tab_length, sum_congr rfl e]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **The share equation over the classes.** The shares of a pair type, each with the number of the further
points of its class, add up to the pair polynomial minus the rooted forms of the two classes at coinciding
points. -/
theorem share_class_sum2 (P : Params) (Q : ℕ) (C : Cert) (a b q : ℕ) (hl : C.last a b < q)
    (hpos : 0 < mult C a b (C.last a b)) (hz : ∀ x, C.last a b < x → x < q → mult C a b x = 0) (w : ℝ) :
    ∑ x ∈ range q, (mult C a b x : ℝ) * shareP2 P Q C a b x w
      = pairH P C a b w - 2 ^ P.aF * (rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, Q, b⟩
          + rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram b, Q, a⟩) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = C.last a b + 1 + r := ⟨q - (C.last a b + 1), by omega⟩
  rw [sum_range_add, sum_range_succ]
  have htail : ∑ x ∈ range r, (mult C a b (C.last a b + 1 + x) : ℝ) * shareP2 P Q C a b (C.last a b + 1 + x) w = 0 := by
    refine sum_eq_zero fun x hx => ?_
    rw [hz (C.last a b + 1 + x) (by omega) (by have := mem_range.mp hx; omega)]
    simp
  have hlow : ∀ x ∈ range (C.last a b), (mult C a b x : ℝ) * shareP2 P Q C a b x w
      = (mult C a b x : ℝ) * (2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b x)) := by
    intro x hx
    rw [shareP2_ne P Q C (Nat.ne_of_lt (mem_range.mp hx))]
  have hmid : (mult C a b (C.last a b) : ℝ) * shareP2 P Q C a b (C.last a b) w
      = shareV P ((2 : ℝ) ^ P.m) w (shareOf2 Q C a b (C.last a b)) := by
    have hm : (shareOf2 Q C a b (C.last a b)).mult = mult C a b (C.last a b) := by rw [shareOf2_last]
    have h0 : ((mult C a b (C.last a b) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    unfold shareP2
    rw [hm, mul_div_cancel₀ _ h0]
  have e2 : ∑ x ∈ range (C.last a b), (mult C a b x : ℝ) * (2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b x))
      = 2 ^ P.aP * ∑ j ∈ range (C.last a b), (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [htail, sum_congr rfl hlow, hmid, shareV2_last, e2]
  unfold pairH
  ring

/-! ## The inequality of a triple type -/

theorem div_ineq2 (c m1 m2 m3 s1 s2 s3 r1 r2 r3 F : ℝ) (h1 : 0 < m1) (h2 : 0 < m2) (h3 : 0 < m3)
    (h : c ≤ (m2 * m3 * s1 + m1 * m3 * s2 + m1 * m2 * s3) - F * (2 * (m1 * m2 * m3)) * (r1 + r2 + r3)) :
    c / (m1 * m2 * m3) ≤ s1 / m1 + s2 / m2 + s3 / m3 - 2 * (F * r1 + F * r2 + F * r3) := by
  have := div_ineq c 1 m1 m2 m3 s1 s2 s3 r1 r2 r3 F one_pos h1 h2 h3 (by rw [one_mul]; exact h)
  simpa using this

/-- **The inequality of a triple type at a point of its domain**, in the terms of the summation. -/
theorem ty_ineq2 (P : Params) (Q : ℕ) (C : Cert) (X : TyX) (hT : TyHolds2 P (tyOf2 Q C X))
    {u v t : ℝ} (h1 : 0 < (shareOf2 Q C X.a X.b X.c).mult) (h2 : 0 < (shareOf2 Q C X.a X.c X.b).mult)
    (h3 : 0 < (shareOf2 Q C X.b X.c X.a).mult) (hu : InBox (C.box X.a X.b) u)
    (hv : InBox (C.box X.a X.c) v) (ht : InBox (C.box X.b X.c) t)
    (hg : ∀ w ∈ X.weights, ∀ g ∈ w.gens, 0 ≤ genV ((2 : ℝ) ^ P.m) u v t g) :
    tyC2 P Q C X ≤ shareP2 P Q C X.a X.b X.c u + shareP2 P Q C X.a X.c X.b v + shareP2 P Q C X.b X.c X.a t
      - 2 * (rootS2 P C X.a X.b X.c u v t + rootS2 P C X.b X.a X.c u t v + rootS2 P C X.c X.a X.b v t u) := by
  obtain ⟨x, hx, rfl⟩ := hu.exists_cube
  obtain ⟨y, hy, rfl⟩ := hv.exists_cube
  obtain ⟨z, hz, rfl⟩ := ht.exists_cube
  have h := hT x y z hx hy hz hg
  unfold lamV2 at h
  push_cast at h
  unfold tyC2 shareP2 rootS2
  exact div_ineq2 _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_pos.mpr h1) (Nat.cast_pos.mpr h2) (Nat.cast_pos.mpr h3) h

/-! ## Points of the sphere -/

/-- `2 ^ m` times the inner product of two points: the variable of the checker. -/
noncomputable def wv3 (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 3)) (i j : ι) : ℝ :=
  (2 : ℝ) ^ m * inner ℝ (x i) (x j)

theorem wv3_comm (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 3)) (i j : ι) : wv3 m x j i = wv3 m x i j := by
  unfold wv3
  rw [real_inner_comm]

theorem wv3_self (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 3)) {i : ι} (hx : ‖x i‖ = 1) :
    wv3 m x i i = (2 : ℝ) ^ m := by
  unfold wv3
  rw [real_inner_self_eq_norm_sq, hx]
  ring

/-- The hypotheses on the data of a typed certificate. `Q` is the index class of the root. -/
structure CertHolds2 (P : Params) (Q : ℕ) (C : Cert) (xs : List TyX) : Prop where
  /-- the index class of the root is the last class, and it is empty -/
  root : Q + 1 = P.q
  empty : C.n Q = 0
  gramLen : ∀ a < Q, (C.gram a).length = P.d + 1
  /-- the Gram matrices of the rooted blocks have the form `Y Yᵀ` -/
  gram : ∀ a < Q, ∃ cols : ℕ → List ℕ,
    ∀ k < (C.gram a).length, GramHolds P (P.d - k) (cols k) ((C.gram a).getD k 0)
  /-- the class of the share equation of a pair type is its largest class with further points -/
  last : ∀ a < P.q, ∀ b < P.q, a ≤ b →
    C.last a b < P.q ∧ 0 < mult C a b (C.last a b) ∧ ∀ x < P.q, C.last a b < x → mult C a b x = 0
  /-- the inequality of every triple type of the list -/
  ty : ∀ X ∈ xs, TyHolds2 P (tyOf2 Q C X)
  /-- the list contains every triple type that occurs -/
  cover : ∀ a < P.q, ∀ b < P.q, ∀ c < P.q, a ≤ b → b ≤ c → 0 < mult C b c a → 0 < mult C a c b →
    0 < mult C a b c → hasX a b c xs = true

/-- Points of the unit sphere of `ℝ³` with classes, in the domain of a typed certificate. -/
structure InDomain2 (P : Params) (C : Cert) (xs : List TyX) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cls : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) : Prop where
  lab : Labelling P.q C cls
  unit : ∀ i, ‖x i‖ = 1
  /-- the inner product of a pair lies in the box of its pair type -/
  box : ∀ i j, i ≠ j → cls i ≤ cls j → InBox (C.box (cls i) (cls j)) (wv3 P.m x i j)
  /-- the generators of the weights of the triple type of a triple are nonnegative -/
  gens : ∀ i j k, Distinct3 i j k → cls i ≤ cls j → cls j ≤ cls k →
    ∀ w ∈ (findX (cls i) (cls j) (cls k) xs).weights, ∀ g ∈ w.gens,
      0 ≤ genV ((2 : ℝ) ^ P.m) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k) g

theorem CertHolds2.root_lt {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (H : CertHolds2 P Q C xs) : Q < P.q := by
  have := H.root
  omega

theorem rootS2_symm {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (H : CertHolds2 P Q C xs) {a b c : ℕ} (ha : a < Q)
    (hb : b < P.q) (hc : c < P.q) (w1 w2 w3 : ℝ) : rootS2 P C a c b w2 w1 w3 = rootS2 P C a b c w1 w2 w3 := by
  obtain ⟨cols, hG⟩ := H.gram a ha
  unfold rootS2
  rw [rootedV2_symm P (C.gram a) cols hG hb hc]

/-- The rooted forms of a root of the class `a` in the share equation of a pair with a point of the class `b`. -/
theorem rootS2_use {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (H : CertHolds2 P Q C xs) {a b : ℕ} (ha : a < Q)
    (hb : b < P.q) (w : ℝ) :
    rootS2 P C a Q b ((2 : ℝ) ^ P.m) w w + rootS2 P C a b Q w ((2 : ℝ) ^ P.m) w + rootS2 P C a b b w w ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, Q, b⟩ := by
  obtain ⟨cols, hG⟩ := H.gram a ha
  have hlen := H.gramLen a ha
  unfold rootS2
  rw [← mul_add, ← mul_add, rootUse2_eq P (C.gram a) cols hG (by omega) H.root_lt hb]

section Points

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}
  {x : ι → EuclideanSpace ℝ (Fin 3)}

/-- The index class of the point `j` in the rooted forms of the root `i`: the class `Q` for the root itself. -/
def clq (Q : ℕ) (cls : ι → ℕ) (i j : ι) : ℕ := if j = i then Q else cls j

theorem clq_self (Q : ℕ) (cls : ι → ℕ) (i : ι) : clq Q cls i i = Q := if_pos rfl

theorem clq_ne (Q : ℕ) (cls : ι → ℕ) {i j : ι} (h : j ≠ i) : clq Q cls i j = cls j := if_neg h

/-- No point has the index class of the root. -/
theorem cls_lt_root (H : CertHolds2 P Q C xs) (L : Labelling P.q C cls) (i : ι) : cls i < Q := by
  have h1 := L.lt i
  have hc := L.card Q H.root_lt
  rw [H.empty, Finset.card_eq_zero] at hc
  have hne : cls i ≠ Q := fun h => by
    have hm : i ∈ univ.filter fun k => cls k = Q := mem_filter.mpr ⟨mem_univ i, h⟩
    rw [hc] at hm
    simp at hm
  have := H.root
  omega

/-- The rooted forms of the root `x i` are positive. -/
theorem rootS2_sum_nonneg (H : CertHolds2 P Q C xs) (hD : InDomain2 P C xs cls x) (i : ι) :
    0 ≤ ∑ j, ∑ k, rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k) := by
  obtain ⟨cols, hG⟩ := H.gram (cls i) (cls_lt_root H hD.lab i)
  have hcl : ∀ j, clq Q cls i j < P.q := fun j => by
    unfold clq
    split_ifs
    · exact H.root_lt
    · exact hD.lab.lt j
  have h := rooted2_root_nonneg P (C.gram (cls i)) cols hG (clq Q cls i) hcl x hD.unit (x i) (hD.unit i) ((2 : ℝ) ^ P.m)
  have e : ∑ j, ∑ k, rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k)
      = 2 ^ P.aF * (∑ j, ∑ k, rootedV2 P ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m * inner ℝ (x i) (x j))
          ((2 : ℝ) ^ P.m * inner ℝ (x i) (x k)) ((2 : ℝ) ^ P.m * inner ℝ (x j) (x k))
          ⟨C.gram (cls i), clq Q cls i j, clq Q cls i k⟩) := by
    simp only [rootS2, wv3, mul_sum]
  rw [e]
  exact mul_nonneg (by positivity) h

/-- The share equation at a pair of points whose classes are in order. -/
theorem share_points2 (H : CertHolds2 P Q C xs) (hD : InDomain2 P C xs cls x) {i j : ι} (hij : i ≠ j)
    (hle : cls i ≤ cls j) :
    (∑ k, if i ≠ k ∧ j ≠ k then shareP2 P Q C (cls i) (cls j) (cls k) (wv3 P.m x i j) else 0)
      = pairH P C (cls i) (cls j) (wv3 P.m x i j)
        - (rootS2 P C (cls i) Q (cls j) (wv3 P.m x i i) (wv3 P.m x i j) (wv3 P.m x i j)
          + rootS2 P C (cls i) (cls j) Q (wv3 P.m x i j) (wv3 P.m x i i) (wv3 P.m x j i)
          + rootS2 P C (cls i) (cls j) (cls j) (wv3 P.m x i j) (wv3 P.m x i j) (wv3 P.m x j j)
          + rootS2 P C (cls j) Q (cls i) (wv3 P.m x j j) (wv3 P.m x j i) (wv3 P.m x j i)
          + rootS2 P C (cls j) (cls i) Q (wv3 P.m x j i) (wv3 P.m x j j) (wv3 P.m x i j)
          + rootS2 P C (cls j) (cls i) (cls i) (wv3 P.m x j i) (wv3 P.m x j i) (wv3 P.m x i i)) := by
  have hi := hD.lab.lt i
  have hj := hD.lab.lt j
  obtain ⟨hl, hpos, hz⟩ := H.last _ hi _ hj hle
  rw [hD.lab.sum_others hij (fun c => shareP2 P Q C (cls i) (cls j) c (wv3 P.m x i j)),
    share_class_sum2 P Q C _ _ _ hl hpos (fun y h1 h2 => hz y h2 h1), wv3_self P.m x (hD.unit i),
    wv3_self P.m x (hD.unit j), wv3_comm P.m x i j]
  have e1 := rootS2_use H (cls_lt_root H hD.lab i) hj (wv3 P.m x i j)
  have e2 := rootS2_use H (cls_lt_root H hD.lab j) hi (wv3 P.m x i j)
  linear_combination e1 + e2

/-- The inequality of the triple type at a triple of points whose classes are in order. -/
theorem lam_points2 (H : CertHolds2 P Q C xs) (hD : InDomain2 P C xs cls x) {i j k : ι} (hd : Distinct3 i j k)
    (hij : cls i ≤ cls j) (hjk : cls j ≤ cls k) :
    tyC2 P Q C (findX (cls i) (cls j) (cls k) xs)
      ≤ shareP2 P Q C (cls i) (cls j) (cls k) (wv3 P.m x i j) + shareP2 P Q C (cls i) (cls k) (cls j) (wv3 P.m x i k)
        + shareP2 P Q C (cls j) (cls k) (cls i) (wv3 P.m x j k)
        - 2 * (rootS2 P C (cls i) (cls j) (cls k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k)
          + rootS2 P C (cls j) (cls i) (cls k) (wv3 P.m x i j) (wv3 P.m x j k) (wv3 P.m x i k)
          + rootS2 P C (cls k) (cls i) (cls j) (wv3 P.m x i k) (wv3 P.m x j k) (wv3 P.m x i j)) := by
  have L := hD.lab
  have m1 : 0 < mult C (cls i) (cls j) (cls k) := L.mult_pos hd
  have m2 : 0 < mult C (cls i) (cls k) (cls j) := L.mult_pos ⟨hd.2.1, hd.1, hd.2.2.symm⟩
  have m3 : 0 < mult C (cls j) (cls k) (cls i) := L.mult_pos ⟨hd.2.2, hd.1.symm, hd.2.1.symm⟩
  obtain ⟨hmem, ha, hb, hc⟩ :=
    findX_spec _ _ _ xs (H.cover _ (L.lt i) _ (L.lt j) _ (L.lt k) hij hjk m3 m2 m1)
  have key := ty_ineq2 P Q C (findX (cls i) (cls j) (cls k) xs) (H.ty _ hmem) (u := wv3 P.m x i j)
    (v := wv3 P.m x i k) (t := wv3 P.m x j k)
  rw [ha, hb, hc] at key
  exact key (shareOf2_mult_pos Q C m1) (shareOf2_mult_pos Q C m2) (shareOf2_mult_pos Q C m3)
    (hD.box i j hd.1 hij) (hD.box i k hd.2.1 (le_trans hij hjk)) (hD.box j k hd.2.2 hjk) (hD.gens i j k hd hij hjk)

/-- **The typed three-point bound on the two-sphere.** For points of the unit sphere of `ℝ³` in the domain of a
typed certificate, the sum of the constants of the triple types over the triples of distinct points is at most
three times the sum of the pair polynomials over the pairs of distinct points plus six times the sum of the
rooted forms of the points at the root. -/
theorem typed_bound2 (H : CertHolds2 P Q C xs) (hD : InDomain2 P C xs cls x) :
    dsum3 (fun i j k => tyC2 P Q C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k))
        (hi3 (cls i) (cls j) (cls k)) xs))
      ≤ 3 * (∑ i, ∑ j, if i ≠ j then
          pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j) else 0)
        + 6 * ∑ i, rootS2 P C (cls i) Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) := by
  have L := hD.lab
  have hQ := fun i => cls_lt_root H L i
  have hw : ∀ i, wv3 P.m x i i = (2 : ℝ) ^ P.m := fun i => wv3_self P.m x (hD.unit i)
  -- the share equation
  have hshare : ∀ i j, i ≠ j →
      (∑ k, if i ≠ k ∧ j ≠ k then
          shareP2 P Q C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv3 P.m x i j) else 0)
        = pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j)
          - (rootS2 P C (cls i) (clq Q cls i i) (clq Q cls i j) (wv3 P.m x i i) (wv3 P.m x i j) (wv3 P.m x i j)
            + rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i i) (wv3 P.m x i j) (wv3 P.m x i i) (wv3 P.m x j i)
            + rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i j) (wv3 P.m x i j) (wv3 P.m x i j) (wv3 P.m x j j)
            + rootS2 P C (cls j) (clq Q cls j j) (clq Q cls j i) (wv3 P.m x j j) (wv3 P.m x j i) (wv3 P.m x j i)
            + rootS2 P C (cls j) (clq Q cls j i) (clq Q cls j j) (wv3 P.m x j i) (wv3 P.m x j j) (wv3 P.m x i j)
            + rootS2 P C (cls j) (clq Q cls j i) (clq Q cls j i) (wv3 P.m x j i) (wv3 P.m x j i) (wv3 P.m x i i)) := by
    intro i j hij
    rw [clq_self, clq_self, clq_ne Q cls hij, clq_ne Q cls (Ne.symm hij)]
    rcases le_total (cls i) (cls j) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      exact share_points2 H hD hij hle
    · have e := share_points2 H hD (Ne.symm hij) hle
      have e' : (∑ k, if i ≠ k ∧ j ≠ k then shareP2 P Q C (cls j) (cls i) (cls k) (wv3 P.m x i j) else 0)
          = ∑ k, if j ≠ k ∧ i ≠ k then shareP2 P Q C (cls j) (cls i) (cls k) (wv3 P.m x i j) else 0 :=
        sum_congr rfl fun k _ => if_congr and_comm rfl rfl
      rw [wv3_comm P.m x i j] at e
      rw [min_eq_right hle, max_eq_left hle, wv3_comm P.m x i j, e', e]
      ring
  -- the inequality of the triple types
  have hlam0 : ∀ i j k, Distinct3 i j k →
      tyC2 P Q C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k)) (hi3 (cls i) (cls j) (cls k)) xs)
        ≤ shareP2 P Q C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv3 P.m x i j)
          + shareP2 P Q C (min (cls i) (cls k)) (max (cls i) (cls k)) (cls j) (wv3 P.m x i k)
          + shareP2 P Q C (min (cls j) (cls k)) (max (cls j) (cls k)) (cls i) (wv3 P.m x j k)
          - 2 * (rootS2 P C (cls i) (cls j) (cls k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k)
            + rootS2 P C (cls j) (cls i) (cls k) (wv3 P.m x j i) (wv3 P.m x j k) (wv3 P.m x i k)
            + rootS2 P C (cls k) (cls i) (cls j) (wv3 P.m x k i) (wv3 P.m x k j) (wv3 P.m x i j)) := by
    refine of_sorted cls _ ?_ ?_ ?_
    · intro i j k hq hd
      have h0 := hq ((distinct3_swap12 i j k).mp hd)
      obtain ⟨a1, a2, a3⟩ := sort3_swap12 (cls i) (cls j) (cls k)
      have e2 : rootS2 P C (cls k) (cls j) (cls i) (wv3 P.m x k j) (wv3 P.m x k i) (wv3 P.m x j i)
          = rootS2 P C (cls k) (cls i) (cls j) (wv3 P.m x k i) (wv3 P.m x k j) (wv3 P.m x i j) := by
        rw [wv3_comm P.m x i j]
        exact rootS2_symm H (hQ k) (L.lt i) (L.lt j) _ _ _
      rw [a1, a2, a3, min_comm (cls j) (cls i), max_comm (cls j) (cls i), e2]
      rw [wv3_comm P.m x i j] at h0 ⊢
      linarith
    · intro i j k hq hd
      have h0 := hq ((distinct3_swap23 i j k).mp hd)
      obtain ⟨a1, a2, a3⟩ := sort3_swap23 (cls i) (cls j) (cls k)
      have e2 : rootS2 P C (cls i) (cls k) (cls j) (wv3 P.m x i k) (wv3 P.m x i j) (wv3 P.m x k j)
          = rootS2 P C (cls i) (cls j) (cls k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k) := by
        rw [wv3_comm P.m x j k]
        exact rootS2_symm H (hQ i) (L.lt j) (L.lt k) _ _ _
      rw [a1, a2, a3, min_comm (cls k) (cls j), max_comm (cls k) (cls j), e2]
      rw [wv3_comm P.m x j k] at h0 ⊢
      linarith
    · intro i j k hij hjk hd
      have h0 := lam_points2 H hD hd hij hjk
      obtain ⟨a1, a2, a3⟩ := sort3_sorted hij hjk
      rw [a1, a2, a3, min_eq_left hij, max_eq_right hij, min_eq_left (le_trans hij hjk),
        max_eq_right (le_trans hij hjk), min_eq_left hjk, max_eq_right hjk, wv3_comm P.m x i j, wv3_comm P.m x i k,
        wv3_comm P.m x j k]
      exact h0
  have hlam : ∀ i j k, Distinct3 i j k →
      tyC2 P Q C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k)) (hi3 (cls i) (cls j) (cls k)) xs)
        ≤ shareP2 P Q C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv3 P.m x i j)
          + shareP2 P Q C (min (cls i) (cls k)) (max (cls i) (cls k)) (cls j) (wv3 P.m x i k)
          + shareP2 P Q C (min (cls j) (cls k)) (max (cls j) (cls k)) (cls i) (wv3 P.m x j k)
          - 2 * (rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k)
            + rootS2 P C (cls j) (clq Q cls j i) (clq Q cls j k) (wv3 P.m x j i) (wv3 P.m x j k) (wv3 P.m x i k)
            + rootS2 P C (cls k) (clq Q cls k i) (clq Q cls k j) (wv3 P.m x k i) (wv3 P.m x k j) (wv3 P.m x i j)) := by
    intro i j k hd
    rw [clq_ne Q cls (Ne.symm hd.1), clq_ne Q cls (Ne.symm hd.2.1), clq_ne Q cls hd.1, clq_ne Q cls (Ne.symm hd.2.2),
      clq_ne Q cls hd.2.1, clq_ne Q cls hd.2.2]
    exact hlam0 i j k hd
  have h := typed_sum
    (fun i j k => rootS2 P C (cls i) (clq Q cls i j) (clq Q cls i k) (wv3 P.m x i j) (wv3 P.m x i k) (wv3 P.m x j k))
    (fun i j k => shareP2 P Q C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv3 P.m x i j))
    (fun i j k => tyC2 P Q C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k))
      (hi3 (cls i) (cls j) (cls k)) xs))
    (fun i j => pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j))
    (rootS2_sum_nonneg H hD) hshare hlam
  simp only [hw, clq_self] at h
  exact h

end Points

/-! ## For the generated modules -/

theorem tyAll2_nil (P : Params) (Q : ℕ) (C : Cert) : ∀ X ∈ ([] : List TyX), TyHolds2 P (tyOf2 Q C X) :=
  fun _ h => by simp at h

theorem tyAll2_cons {P : Params} {Q : ℕ} {C : Cert} {X : TyX} {l : List TyX} (h : TyHolds2 P (tyOf2 Q C X))
    (hl : ∀ Y ∈ l, TyHolds2 P (tyOf2 Q C Y)) : ∀ Y ∈ X :: l, TyHolds2 P (tyOf2 Q C Y) := by
  intro Y hY
  rcases List.mem_cons.mp hY with rfl | hY
  · exact h
  · exact hl Y hY

end N11.Circ
