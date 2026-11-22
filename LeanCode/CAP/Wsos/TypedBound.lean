module

public import CAP.Wsos.Sound
public import CAP.Wsos.Sphere3
public import CAP.Wsos.Classes

/-!
# The typed three-point bound on the unit sphere of `ℝ⁴`

Let `C` be the data of a typed certificate and `xs` the list of its triple types, and let

* the Gram matrices of the rooted blocks have the form `Y Yᵀ` (`GramHolds`),
* the inequality of every triple type of the list hold (`TyHolds`),
* the list contain every triple type that occurs, and the class `last a b` of every pair type be the
  largest class with further points

(`CertHolds`). Let points `x i` of the unit sphere of `ℝ⁴` be labelled by classes with the sizes of
the certificate, such that the inner products of all pairs lie in the boxes of their pair types and
the generators of the weights of all triples are nonnegative (`InDomain`).

`typed_bound`: then the sum of the constants of the triple types over the triples of points is at
most `3 ∑ i ≠ j, H (x i, x j) + 6 ∑ i, s (x i; x i, x i)`, where `H` is the pair polynomial of the
classes of the two points and `s` the rooted form. All quantities are in the unit `2 ^ K` of the
checker, and the variables are `2 ^ m` times the inner products (`wv`).

The proof verifies the three hypotheses of `typed_sum`: the positivity of the rooted forms
(`rooted_root_nonneg`), the share equation (`share_class_sum`, `Labelling.sum_others`, `rootUse_eq`)
and the inequality of the triple types (`ty_ineq`, from `TyHolds`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

/-! ## Values in the unit `2 ^ K` -/

/-- The share of the pair type `(a, b)` for one point of the class `c`. -/
noncomputable def shareP (P : Params) (C : Cert) (a b c : ℕ) (w : ℝ) : ℝ :=
  shareV P ((2 : ℝ) ^ P.m) w (shareOf C a b c) / ((shareOf C a b c).mult : ℝ)

/-- The pair polynomial of the pair type `(a, b)`. -/
noncomputable def pairH (P : Params) (C : Cert) (a b : ℕ) (w : ℝ) : ℝ :=
  2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.H a b)

/-- The rooted form of a root of the class `a` at points of the classes `b` and `c`. -/
noncomputable def rootS (P : Params) (C : Cert) (a b c : ℕ) (w1 w2 w3 : ℝ) : ℝ :=
  2 ^ P.aF * rootedV P ((2 : ℝ) ^ P.m) w1 w2 w3 ⟨C.gram a, b, c⟩ / (P.d.factorial : ℝ)

/-- The constant of a triple type. -/
noncomputable def tyC (P : Params) (C : Cert) (X : TyX) : ℝ :=
  ((X.c2p : ℝ) - (X.c2n : ℝ)) / ((P.d.factorial : ℝ)
    * (((shareOf C X.a X.b X.c).mult : ℝ) * ((shareOf C X.a X.c X.b).mult : ℝ) * ((shareOf C X.b X.c X.a).mult : ℝ)))

/-! ## The shares of a pair type -/

theorem shareOf_last (C : Cert) (a b : ℕ) : shareOf C a b (C.last a b)
    = ⟨mult C a b (C.last a b), C.H a b, tab (C.p a b) (C.last a b), tab (mult C a b) (C.last a b),
        [⟨C.gram a, a, b⟩, ⟨C.gram b, b, a⟩]⟩ := by
  unfold shareOf
  rw [Nat.beq_refl]
  rfl

theorem shareOf_ne (C : Cert) {a b c : ℕ} (hc : c ≠ C.last a b) : shareOf C a b c = ⟨1, C.p a b c, [], [], []⟩ := by
  have hb : Nat.beq c (C.last a b) = false := by
    cases hb : Nat.beq c (C.last a b) with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hc
  unfold shareOf
  rw [hb]
  rfl

theorem shareOf_mult_pos (C : Cert) {a b c : ℕ} (h : 0 < mult C a b c) : 0 < (shareOf C a b c).mult := by
  by_cases hc : c = C.last a b
  · rw [hc, shareOf_last]
    rw [hc] at h
    exact h
  · rw [shareOf_ne C hc]
    exact Nat.one_pos

theorem shareP_ne (P : Params) (C : Cert) {a b c : ℕ} (hc : c ≠ C.last a b) (w : ℝ) :
    shareP P C a b c w = 2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b c) := by
  unfold shareP
  rw [shareOf_ne C hc]
  simp [shareV]

theorem shareV_last (P : Params) (C : Cert) (a b : ℕ) (w : ℝ) :
    shareV P ((2 : ℝ) ^ P.m) w (shareOf C a b (C.last a b))
      = 2 ^ P.aP * (spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.H a b)
          - ∑ j ∈ range (C.last a b), (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j))
        - 2 ^ P.aF * (rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, a, b⟩ + rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram b, b, a⟩) := by
  have e : ∀ j ∈ range (C.last a b),
      (((tab (mult C a b) (C.last a b)).getD j 0 : ℕ) : ℝ)
          * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D ((tab (C.p a b) (C.last a b)).getD j 0)
        = (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j) :=
    fun j hj => by rw [tab_getD _ (mem_range.mp hj), tab_getD _ (mem_range.mp hj)]
  rw [shareOf_last]
  unfold shareV
  dsimp only
  rw [tab_length, sum_congr rfl e]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **The share equation over the classes.** The shares of a pair type, each with the number of the
further points of its class, add up to the pair polynomial minus the rooted forms of the two classes
at coinciding points. -/
theorem share_class_sum (P : Params) (C : Cert) (a b q : ℕ) (hl : C.last a b < q)
    (hpos : 0 < mult C a b (C.last a b)) (hz : ∀ x, C.last a b < x → x < q → mult C a b x = 0) (w : ℝ) :
    ∑ x ∈ range q, (mult C a b x : ℝ) * shareP P C a b x w
      = pairH P C a b w - 2 ^ P.aF * (rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, a, b⟩
          + rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram b, b, a⟩) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = C.last a b + 1 + r := ⟨q - (C.last a b + 1), by omega⟩
  rw [sum_range_add, sum_range_succ]
  have htail : ∑ x ∈ range r, (mult C a b (C.last a b + 1 + x) : ℝ) * shareP P C a b (C.last a b + 1 + x) w = 0 := by
    refine sum_eq_zero fun x hx => ?_
    rw [hz (C.last a b + 1 + x) (by omega) (by have := mem_range.mp hx; omega)]
    simp
  have hlow : ∀ x ∈ range (C.last a b), (mult C a b x : ℝ) * shareP P C a b x w
      = (mult C a b x : ℝ) * (2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b x)) := by
    intro x hx
    rw [shareP_ne P C (Nat.ne_of_lt (mem_range.mp hx))]
  have hmid : (mult C a b (C.last a b) : ℝ) * shareP P C a b (C.last a b) w
      = shareV P ((2 : ℝ) ^ P.m) w (shareOf C a b (C.last a b)) := by
    have hm : (shareOf C a b (C.last a b)).mult = mult C a b (C.last a b) := by rw [shareOf_last]
    have h0 : ((mult C a b (C.last a b) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    unfold shareP
    rw [hm, mul_div_cancel₀ _ h0]
  have e2 : ∑ x ∈ range (C.last a b), (mult C a b x : ℝ) * (2 ^ P.aP * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b x))
      = 2 ^ P.aP * ∑ j ∈ range (C.last a b), (mult C a b j : ℝ) * spolyV P.wP ((2 : ℝ) ^ P.m) w P.D (C.p a b j) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [htail, sum_congr rfl hlow, hmid, shareV_last, e2]
  unfold pairH
  ring

/-! ## The inequality of a triple type -/

/-- The variable `w` lies in the box: `|w - c| ≤ ρ`. -/
def InBox (b : Box) (w : ℝ) : Prop := |w - ((b.cp : ℝ) - (b.cn : ℝ))| ≤ (b.rho : ℝ)

theorem InBox.exists_cube {b : Box} {w : ℝ} (h : InBox b w) : ∃ x : ℝ, |x| ≤ 1 ∧ affV b x = w := by
  unfold InBox at h
  by_cases h0 : (b.rho : ℝ) = 0
  · refine ⟨0, by simp, ?_⟩
    rw [h0] at h
    have e : w - ((b.cp : ℝ) - (b.cn : ℝ)) = 0 := abs_nonpos_iff.mp h
    unfold affV
    rw [h0]
    linarith
  · have hpos : (0 : ℝ) < b.rho := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
    refine ⟨(w - ((b.cp : ℝ) - (b.cn : ℝ))) / b.rho, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact h
    · unfold affV
      rw [mul_div_cancel₀ _ h0]
      ring

theorem div_ineq (c d m1 m2 m3 s1 s2 s3 r1 r2 r3 F : ℝ) (hd : 0 < d) (h1 : 0 < m1) (h2 : 0 < m2) (h3 : 0 < m3)
    (h : c ≤ d * (m2 * m3 * s1 + m1 * m3 * s2 + m1 * m2 * s3) - F * (2 * (m1 * m2 * m3)) * (r1 + r2 + r3)) :
    c / (d * (m1 * m2 * m3)) ≤ s1 / m1 + s2 / m2 + s3 / m3 - 2 * (F * r1 / d + F * r2 / d + F * r3 / d) := by
  rw [div_le_iff₀ (by positivity)]
  have e : (s1 / m1 + s2 / m2 + s3 / m3 - 2 * (F * r1 / d + F * r2 / d + F * r3 / d)) * (d * (m1 * m2 * m3))
      = d * (m2 * m3 * s1 + m1 * m3 * s2 + m1 * m2 * s3) - F * (2 * (m1 * m2 * m3)) * (r1 + r2 + r3) := by
    field_simp
  rw [e]
  exact h

/-- **The inequality of a triple type at a point of its domain**, in the terms of the summation. -/
theorem ty_ineq (P : Params) (C : Cert) (X : TyX) (hT : TyHolds P (tyOf C X))
    {u v t : ℝ} (h1 : 0 < (shareOf C X.a X.b X.c).mult) (h2 : 0 < (shareOf C X.a X.c X.b).mult)
    (h3 : 0 < (shareOf C X.b X.c X.a).mult) (hu : InBox (C.box X.a X.b) u)
    (hv : InBox (C.box X.a X.c) v) (ht : InBox (C.box X.b X.c) t)
    (hg : ∀ w ∈ X.weights, ∀ g ∈ w.gens, 0 ≤ genV ((2 : ℝ) ^ P.m) u v t g) :
    tyC P C X ≤ shareP P C X.a X.b X.c u + shareP P C X.a X.c X.b v + shareP P C X.b X.c X.a t
      - 2 * (rootS P C X.a X.b X.c u v t + rootS P C X.b X.a X.c u t v + rootS P C X.c X.a X.b v t u) := by
  obtain ⟨x, hx, rfl⟩ := hu.exists_cube
  obtain ⟨y, hy, rfl⟩ := hv.exists_cube
  obtain ⟨z, hz, rfl⟩ := ht.exists_cube
  have h := hT x y z hx hy hz hg
  unfold lamV at h
  rw [fact_eq] at h
  push_cast at h
  unfold tyC shareP rootS
  exact div_ineq _ _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_pos.mpr (Nat.factorial_pos _)) (Nat.cast_pos.mpr h1)
    (Nat.cast_pos.mpr h2) (Nat.cast_pos.mpr h3) h

/-! ## Points of the sphere -/

/-- `2 ^ m` times the inner product of two points: the variable of the checker. -/
noncomputable def wv (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 4)) (i j : ι) : ℝ :=
  (2 : ℝ) ^ m * inner ℝ (x i) (x j)

theorem wv_comm (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 4)) (i j : ι) : wv m x j i = wv m x i j := by
  unfold wv
  rw [real_inner_comm]

theorem wv_self (m : ℕ) {ι : Type*} (x : ι → EuclideanSpace ℝ (Fin 4)) {i : ι} (hx : ‖x i‖ = 1) :
    wv m x i i = (2 : ℝ) ^ m := by
  unfold wv
  rw [real_inner_self_eq_norm_sq, hx]
  ring

/-- The hypotheses on the data of a typed certificate. -/
structure CertHolds (P : Params) (C : Cert) (xs : List TyX) : Prop where
  /-- the kernels are known to be positive up to the degree `8` -/
  deg : P.d ≤ 8
  gramLen : ∀ a < P.q, (C.gram a).length = P.d + 1
  /-- the Gram matrices of the rooted blocks have the form `Y Yᵀ` -/
  gram : ∀ a < P.q, ∃ cols : ℕ → List ℕ,
    ∀ k < (C.gram a).length, GramHolds P (P.d - k) (cols k) ((C.gram a).getD k 0)
  /-- the class of the share equation of a pair type is its largest class with further points -/
  last : ∀ a < P.q, ∀ b < P.q, a ≤ b →
    C.last a b < P.q ∧ 0 < mult C a b (C.last a b) ∧ ∀ x < P.q, C.last a b < x → mult C a b x = 0
  /-- the inequality of every triple type of the list -/
  ty : ∀ X ∈ xs, TyHolds P (tyOf C X)
  /-- the list contains every triple type that occurs -/
  cover : ∀ a < P.q, ∀ b < P.q, ∀ c < P.q, a ≤ b → b ≤ c → 0 < mult C b c a → 0 < mult C a c b →
    0 < mult C a b c → hasX a b c xs = true

/-- Points of the unit sphere of `ℝ⁴` with classes, in the domain of a typed certificate. -/
structure InDomain (P : Params) (C : Cert) (xs : List TyX) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cls : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 4)) : Prop where
  lab : Labelling P.q C cls
  unit : ∀ i, ‖x i‖ = 1
  /-- the inner product of a pair lies in the box of its pair type -/
  box : ∀ i j, i ≠ j → cls i ≤ cls j → InBox (C.box (cls i) (cls j)) (wv P.m x i j)
  /-- the generators of the weights of the triple type of a triple are nonnegative -/
  gens : ∀ i j k, Distinct3 i j k → cls i ≤ cls j → cls j ≤ cls k →
    ∀ w ∈ (findX (cls i) (cls j) (cls k) xs).weights, ∀ g ∈ w.gens,
      0 ≤ genV ((2 : ℝ) ^ P.m) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k) g

theorem rootS_symm {P : Params} {C : Cert} {xs : List TyX} (H : CertHolds P C xs) {a b c : ℕ} (ha : a < P.q)
    (hb : b < P.q) (hc : c < P.q) (w1 w2 w3 : ℝ) : rootS P C a c b w2 w1 w3 = rootS P C a b c w1 w2 w3 := by
  obtain ⟨cols, hG⟩ := H.gram a ha
  unfold rootS
  rw [rootedV_symm P (C.gram a) cols hG hb hc]

/-- The rooted forms of a root of the class `a` in the share equation of a pair with a point of the class `b`. -/
theorem rootS_use {P : Params} {C : Cert} {xs : List TyX} (H : CertHolds P C xs) {a b : ℕ} (ha : a < P.q)
    (hb : b < P.q) (w : ℝ) :
    rootS P C a a b ((2 : ℝ) ^ P.m) w w + rootS P C a b a w ((2 : ℝ) ^ P.m) w + rootS P C a b b w w ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * rootUseV P ((2 : ℝ) ^ P.m) w ⟨C.gram a, a, b⟩ := by
  obtain ⟨cols, hG⟩ := H.gram a ha
  have hlen := H.gramLen a ha
  have hne : ((P.d.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  unfold rootS
  rw [← add_div, ← add_div, ← mul_add, ← mul_add, rootUse_eq P (C.gram a) cols hG (by omega) (by omega) ha hb]
  field_simp

section Points

variable {P : Params} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}
  {x : ι → EuclideanSpace ℝ (Fin 4)}

/-- The rooted forms of the root `x i` are positive. -/
theorem rootS_sum_nonneg (H : CertHolds P C xs) (hD : InDomain P C xs cls x) (i : ι) :
    0 ≤ ∑ j, ∑ k, rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k) := by
  obtain ⟨cols, hG⟩ := H.gram (cls i) (hD.lab.lt i)
  have hlen := H.gramLen (cls i) (hD.lab.lt i)
  have h := rooted_root_nonneg P (C.gram (cls i)) cols (by have := H.deg; omega) hG cls hD.lab.lt x hD.unit
    (x i) (hD.unit i) ((2 : ℝ) ^ P.m)
  have e : ∑ j, ∑ k, rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k)
      = 2 ^ P.aF * (∑ j, ∑ k, rootedV P ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m * inner ℝ (x i) (x j))
          ((2 : ℝ) ^ P.m * inner ℝ (x i) (x k)) ((2 : ℝ) ^ P.m * inner ℝ (x j) (x k)) ⟨C.gram (cls i), cls j, cls k⟩)
        / (P.d.factorial : ℝ) := by
    simp only [rootS, wv, mul_sum, sum_div]
  rw [e]
  exact div_nonneg (mul_nonneg (by positivity) h) (Nat.cast_nonneg _)

/-- The share equation at a pair of points whose classes are in order. -/
theorem share_points (H : CertHolds P C xs) (hD : InDomain P C xs cls x) {i j : ι} (hij : i ≠ j)
    (hle : cls i ≤ cls j) :
    (∑ k, if i ≠ k ∧ j ≠ k then shareP P C (cls i) (cls j) (cls k) (wv P.m x i j) else 0)
      = pairH P C (cls i) (cls j) (wv P.m x i j)
        - (rootS P C (cls i) (cls i) (cls j) (wv P.m x i i) (wv P.m x i j) (wv P.m x i j)
          + rootS P C (cls i) (cls j) (cls i) (wv P.m x i j) (wv P.m x i i) (wv P.m x j i)
          + rootS P C (cls i) (cls j) (cls j) (wv P.m x i j) (wv P.m x i j) (wv P.m x j j)
          + rootS P C (cls j) (cls j) (cls i) (wv P.m x j j) (wv P.m x j i) (wv P.m x j i)
          + rootS P C (cls j) (cls i) (cls j) (wv P.m x j i) (wv P.m x j j) (wv P.m x i j)
          + rootS P C (cls j) (cls i) (cls i) (wv P.m x j i) (wv P.m x j i) (wv P.m x i i)) := by
  have hi := hD.lab.lt i
  have hj := hD.lab.lt j
  obtain ⟨hl, hpos, hz⟩ := H.last _ hi _ hj hle
  rw [hD.lab.sum_others hij (fun c => shareP P C (cls i) (cls j) c (wv P.m x i j)),
    share_class_sum P C _ _ _ hl hpos (fun y h1 h2 => hz y h2 h1), wv_self P.m x (hD.unit i), wv_self P.m x (hD.unit j), wv_comm P.m x i j]
  have e1 := rootS_use H hi hj (wv P.m x i j)
  have e2 := rootS_use H hj hi (wv P.m x i j)
  linear_combination e1 + e2

/-- The inequality of the triple type at a triple of points whose classes are in order. -/
theorem lam_points (H : CertHolds P C xs) (hD : InDomain P C xs cls x) {i j k : ι} (hd : Distinct3 i j k)
    (hij : cls i ≤ cls j) (hjk : cls j ≤ cls k) :
    tyC P C (findX (cls i) (cls j) (cls k) xs)
      ≤ shareP P C (cls i) (cls j) (cls k) (wv P.m x i j) + shareP P C (cls i) (cls k) (cls j) (wv P.m x i k)
        + shareP P C (cls j) (cls k) (cls i) (wv P.m x j k)
        - 2 * (rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k)
          + rootS P C (cls j) (cls i) (cls k) (wv P.m x i j) (wv P.m x j k) (wv P.m x i k)
          + rootS P C (cls k) (cls i) (cls j) (wv P.m x i k) (wv P.m x j k) (wv P.m x i j)) := by
  have L := hD.lab
  have m1 : 0 < mult C (cls i) (cls j) (cls k) := L.mult_pos hd
  have m2 : 0 < mult C (cls i) (cls k) (cls j) := L.mult_pos ⟨hd.2.1, hd.1, hd.2.2.symm⟩
  have m3 : 0 < mult C (cls j) (cls k) (cls i) := L.mult_pos ⟨hd.2.2, hd.1.symm, hd.2.1.symm⟩
  obtain ⟨hmem, ha, hb, hc⟩ :=
    findX_spec _ _ _ xs (H.cover _ (L.lt i) _ (L.lt j) _ (L.lt k) hij hjk m3 m2 m1)
  have key := ty_ineq P C (findX (cls i) (cls j) (cls k) xs) (H.ty _ hmem) (u := wv P.m x i j)
    (v := wv P.m x i k) (t := wv P.m x j k)
  rw [ha, hb, hc] at key
  exact key (shareOf_mult_pos C m1) (shareOf_mult_pos C m2) (shareOf_mult_pos C m3)
    (hD.box i j hd.1 hij) (hD.box i k hd.2.1 (le_trans hij hjk)) (hD.box j k hd.2.2 hjk) (hD.gens i j k hd hij hjk)

/-- **The typed three-point bound.** For points of the unit sphere of `ℝ⁴` in the domain of a typed
certificate, the sum of the constants of the triple types over the triples of distinct points is at
most three times the sum of the pair polynomials over the pairs of distinct points plus six times
the sum of the rooted forms at coinciding points. -/
theorem typed_bound (H : CertHolds P C xs) (hD : InDomain P C xs cls x) :
    dsum3 (fun i j k => tyC P C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k))
        (hi3 (cls i) (cls j) (cls k)) xs))
      ≤ 3 * (∑ i, ∑ j, if i ≠ j then
          pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j) else 0)
        + 6 * ∑ i, rootS P C (cls i) (cls i) (cls i) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) := by
  have L := hD.lab
  have hw : ∀ i, wv P.m x i i = (2 : ℝ) ^ P.m := fun i => wv_self P.m x (hD.unit i)
  -- the share equation
  have hshare : ∀ i j, i ≠ j →
      (∑ k, if i ≠ k ∧ j ≠ k then
          shareP P C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv P.m x i j) else 0)
        = pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j)
          - (rootS P C (cls i) (cls i) (cls j) (wv P.m x i i) (wv P.m x i j) (wv P.m x i j)
            + rootS P C (cls i) (cls j) (cls i) (wv P.m x i j) (wv P.m x i i) (wv P.m x j i)
            + rootS P C (cls i) (cls j) (cls j) (wv P.m x i j) (wv P.m x i j) (wv P.m x j j)
            + rootS P C (cls j) (cls j) (cls i) (wv P.m x j j) (wv P.m x j i) (wv P.m x j i)
            + rootS P C (cls j) (cls i) (cls j) (wv P.m x j i) (wv P.m x j j) (wv P.m x i j)
            + rootS P C (cls j) (cls i) (cls i) (wv P.m x j i) (wv P.m x j i) (wv P.m x i i)) := by
    intro i j hij
    rcases le_total (cls i) (cls j) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      exact share_points H hD hij hle
    · have e := share_points H hD (Ne.symm hij) hle
      have e' : (∑ k, if i ≠ k ∧ j ≠ k then shareP P C (cls j) (cls i) (cls k) (wv P.m x i j) else 0)
          = ∑ k, if j ≠ k ∧ i ≠ k then shareP P C (cls j) (cls i) (cls k) (wv P.m x i j) else 0 :=
        sum_congr rfl fun k _ => if_congr and_comm rfl rfl
      rw [wv_comm P.m x i j] at e
      rw [min_eq_right hle, max_eq_left hle, wv_comm P.m x i j, e', e]
      ring
  -- the inequality of the triple types
  have hlam : ∀ i j k, Distinct3 i j k →
      tyC P C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k)) (hi3 (cls i) (cls j) (cls k)) xs)
        ≤ shareP P C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv P.m x i j)
          + shareP P C (min (cls i) (cls k)) (max (cls i) (cls k)) (cls j) (wv P.m x i k)
          + shareP P C (min (cls j) (cls k)) (max (cls j) (cls k)) (cls i) (wv P.m x j k)
          - 2 * (rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k)
            + rootS P C (cls j) (cls i) (cls k) (wv P.m x j i) (wv P.m x j k) (wv P.m x i k)
            + rootS P C (cls k) (cls i) (cls j) (wv P.m x k i) (wv P.m x k j) (wv P.m x i j)) := by
    refine of_sorted cls _ ?_ ?_ ?_
    · intro i j k hq hd
      have h0 := hq ((distinct3_swap12 i j k).mp hd)
      obtain ⟨a1, a2, a3⟩ := sort3_swap12 (cls i) (cls j) (cls k)
      have e2 : rootS P C (cls k) (cls j) (cls i) (wv P.m x k j) (wv P.m x k i) (wv P.m x j i)
          = rootS P C (cls k) (cls i) (cls j) (wv P.m x k i) (wv P.m x k j) (wv P.m x i j) := by
        rw [wv_comm P.m x i j]
        exact rootS_symm H (L.lt k) (L.lt i) (L.lt j) _ _ _
      rw [a1, a2, a3, min_comm (cls j) (cls i), max_comm (cls j) (cls i), e2]
      rw [wv_comm P.m x i j] at h0 ⊢
      linarith
    · intro i j k hq hd
      have h0 := hq ((distinct3_swap23 i j k).mp hd)
      obtain ⟨a1, a2, a3⟩ := sort3_swap23 (cls i) (cls j) (cls k)
      have e2 : rootS P C (cls i) (cls k) (cls j) (wv P.m x i k) (wv P.m x i j) (wv P.m x k j)
          = rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k) := by
        rw [wv_comm P.m x j k]
        exact rootS_symm H (L.lt i) (L.lt j) (L.lt k) _ _ _
      rw [a1, a2, a3, min_comm (cls k) (cls j), max_comm (cls k) (cls j), e2]
      rw [wv_comm P.m x j k] at h0 ⊢
      linarith
    · intro i j k hij hjk hd
      have h0 := lam_points H hD hd hij hjk
      obtain ⟨a1, a2, a3⟩ := sort3_sorted hij hjk
      rw [a1, a2, a3, min_eq_left hij, max_eq_right hij, min_eq_left (le_trans hij hjk),
        max_eq_right (le_trans hij hjk), min_eq_left hjk, max_eq_right hjk, wv_comm P.m x i j, wv_comm P.m x i k,
        wv_comm P.m x j k]
      exact h0
  have h := typed_sum
    (fun i j k => rootS P C (cls i) (cls j) (cls k) (wv P.m x i j) (wv P.m x i k) (wv P.m x j k))
    (fun i j k => shareP P C (min (cls i) (cls j)) (max (cls i) (cls j)) (cls k) (wv P.m x i j))
    (fun i j k => tyC P C (findX (lo3 (cls i) (cls j) (cls k)) (mid3 (cls i) (cls j) (cls k))
      (hi3 (cls i) (cls j) (cls k)) xs))
    (fun i j => pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j))
    (rootS_sum_nonneg H hD) hshare hlam
  simp only [hw] at h
  exact h

end Points

/-! ## For the generated modules -/

/-- The Gram matrices of a class, for the degrees `n, n - 1, …`, have the form `Y Yᵀ`. -/
def GramAll (P : Params) : ℕ → List (List ℕ) → List ℕ → Prop
  | _, [], [] => True
  | n, y :: ys, g :: gs => GramHolds P n y g ∧ GramAll P (n - 1) ys gs
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False

theorem GramAll.holds {P : Params} : ∀ {n : ℕ} {ys : List (List ℕ)} {g : List ℕ}, GramAll P n ys g →
    ∀ k < g.length, GramHolds P (n - k) (nthL ys k) (g.getD k 0)
  | _, [], [], _, k, hk => by simp at hk
  | _, _ :: _, _ :: _, h, 0, _ => h.1
  | n, y :: ys, g :: gs, h, k + 1, hk => by
    have h' := GramAll.holds h.2 k (by simpa using hk)
    rw [show n - (k + 1) = n - 1 - k by omega]
    exact h'
  | _, [], _ :: _, h, _, _ => h.elim
  | _, _ :: _, [], h, _, _ => h.elim

theorem gram_of_all {P : Params} {ys : List (List ℕ)} {g : List ℕ} (h : GramAll P P.d ys g) :
    ∃ cols : ℕ → List ℕ, ∀ k < g.length, GramHolds P (P.d - k) (cols k) (g.getD k 0) :=
  ⟨nthL ys, h.holds⟩

theorem tyAll_nil (P : Params) (C : Cert) : ∀ X ∈ ([] : List TyX), TyHolds P (tyOf C X) :=
  fun _ h => by simp at h

theorem tyAll_cons {P : Params} {C : Cert} {X : TyX} {l : List TyX} (h : TyHolds P (tyOf C X))
    (hl : ∀ Y ∈ l, TyHolds P (tyOf C Y)) : ∀ Y ∈ X :: l, TyHolds P (tyOf C Y) := by
  intro Y hY
  rcases List.mem_cons.mp hY with rfl | hY
  · exact h
  · exact hl Y hY

end CAP.Wsos
