module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import CAP.Wsos.Cert
public import CAP.Wsos.TypedSum

/-!
# Points with classes

A *labelling* assigns a class below `q` to every point of a finite set, such that the class `x` has
`C.n x` points. For two distinct points `i`, `j` the number `mult C (cls i) (cls j) x` of the
certificate is the number of the further points of the class `x` (`Labelling.mult_card`). Hence a
sum over the further points of a function of their classes is a sum over the classes
(`Labelling.sum_others`), and the multiplicity of the class of a third point is positive
(`Labelling.mult_pos`).

The file also contains the lemmas on the tables of `Cert.lean` (`tab`, `findX`, `hasX`) and the
reduction of a symmetric statement on triples to triples with sorted classes (`of_sorted`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

/-! ## The functions of `Cert.lean` -/

theorem cond_beq (x a : ℕ) : cond (Nat.beq x a) 1 0 = if x = a then 1 else 0 := by
  by_cases h : x = a
  · subst h
    rw [if_pos rfl, Nat.beq_refl]
    rfl
  · have hb : Nat.beq x a = false := by
      cases hb : Nat.beq x a with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [if_neg h, hb]
    rfl

theorem mult_eq (C : Cert) (a b x : ℕ) :
    mult C a b x = C.n x - (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  show Nat.sub (Nat.sub (C.n x) (cond (Nat.beq x a) 1 0)) (cond (Nat.beq x b) 1 0) = _
  rw [cond_beq, cond_beq]
  rfl

theorem mult_comm (C : Cert) (a b x : ℕ) : mult C b a x = mult C a b x := by
  rw [mult_eq, mult_eq]
  omega

theorem tabGo_eq (f : ℕ → ℕ) : ∀ (n : ℕ) (acc : List ℕ), tabGo f n acc = (List.range n).map f ++ acc
  | 0, acc => rfl
  | n + 1, acc => by
    show tabGo f n (f n :: acc) = _
    rw [tabGo_eq f n, List.range_succ, List.map_append, List.append_assoc]
    rfl

theorem tab_eq (f : ℕ → ℕ) (n : ℕ) : tab f n = (List.range n).map f := by
  unfold tab
  rw [tabGo_eq, List.append_nil]

theorem tab_length (f : ℕ → ℕ) (n : ℕ) : (tab f n).length = n := by
  rw [tab_eq, List.length_map, List.length_range]

theorem tab_getD (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) : (tab f n).getD i 0 = f i := by
  rw [tab_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem isKey_iff (a b c : ℕ) (X : TyX) : isKey a b c X = true ↔ X.a = a ∧ X.b = b ∧ X.c = c := by
  unfold isKey
  rw [Bool.and_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact ⟨⟨Nat.beq_refl a, Nat.beq_refl b⟩, Nat.beq_refl c⟩

/-- If a list has an entry for a triple type, then `findX` returns such an entry. -/
theorem findX_spec (a b c : ℕ) : ∀ xs : List TyX, hasX a b c xs = true →
    findX a b c xs ∈ xs ∧ (findX a b c xs).a = a ∧ (findX a b c xs).b = b ∧ (findX a b c xs).c = c
  | [], h => by cases h
  | X :: xs, h => by
    cases hk : isKey a b c X with
    | true =>
      have e : findX a b c (X :: xs) = X := by
        show cond (isKey a b c X) X (findX a b c xs) = X
        rw [hk]
        rfl
      rw [e]
      exact ⟨List.mem_cons_self, (isKey_iff a b c X).mp hk⟩
    | false =>
      have e : findX a b c (X :: xs) = findX a b c xs := by
        show cond (isKey a b c X) X (findX a b c xs) = _
        rw [hk]
        rfl
      have h' : hasX a b c xs = true := by
        have : hasX a b c (X :: xs) = cond (isKey a b c X) true (hasX a b c xs) := rfl
        rw [this, hk] at h
        exact h
      rw [e]
      obtain ⟨h1, h2⟩ := findX_spec a b c xs h'
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-! ## Sorted triples -/

/-- A statement on triples that is invariant under the exchange of two neighbours holds for all
triples if it holds for the triples with sorted values of `f`. -/
theorem of_sorted {ι : Type*} (f : ι → ℕ) (Q : ι → ι → ι → Prop) (h12 : ∀ i j k, Q i j k → Q j i k)
    (h23 : ∀ i j k, Q i j k → Q i k j) (hs : ∀ i j k, f i ≤ f j → f j ≤ f k → Q i j k) : ∀ i j k, Q i j k := by
  intro i j k
  rcases le_total (f i) (f j) with hij | hij <;> rcases le_total (f j) (f k) with hjk | hjk <;>
    rcases le_total (f i) (f k) with hik | hik
  · exact hs i j k hij hjk
  · exact hs i j k hij hjk
  · exact h23 _ _ _ (hs i k j hik hjk)
  · exact h23 _ _ _ (h12 _ _ _ (hs k i j hik hij))
  · exact h12 _ _ _ (hs j i k hij hik)
  · exact h12 _ _ _ (h23 _ _ _ (hs j k i hjk hik))
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs k j i hjk hij)))
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs k j i hjk hij)))

theorem min2_eq (a b : ℕ) : min2 a b = min a b := by
  unfold min2
  cases h : Nat.ble a b with
  | true => exact (Nat.min_eq_left (Nat.le_of_ble_eq_true h)).symm
  | false =>
    have h' : ¬ a ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; cases h
    exact (Nat.min_eq_right (Nat.le_of_not_le h')).symm

theorem max2_eq (a b : ℕ) : max2 a b = max a b := by
  unfold max2
  cases h : Nat.ble a b with
  | true => exact (Nat.max_eq_right (Nat.le_of_ble_eq_true h)).symm
  | false =>
    have h' : ¬ a ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; cases h
    exact (Nat.max_eq_left (Nat.le_of_not_le h')).symm

/-- The smallest, the middle and the largest of three numbers (`Cert.lean`). -/
theorem lo3_eq (a b c : ℕ) : lo3 a b c = min a (min b c) := by
  unfold lo3
  rw [min2_eq, min2_eq]

theorem hi3_eq (a b c : ℕ) : hi3 a b c = max a (max b c) := by
  unfold hi3
  rw [max2_eq, max2_eq]

theorem mid3_eq (a b c : ℕ) : mid3 a b c = a + b + c - min a (min b c) - max a (max b c) := by
  show a + b + c - lo3 a b c - hi3 a b c = _
  rw [lo3_eq, hi3_eq]

theorem sort3_swap12 (a b c : ℕ) : lo3 b a c = lo3 a b c ∧ mid3 b a c = mid3 a b c ∧ hi3 b a c = hi3 a b c := by
  simp only [mid3_eq, lo3_eq, hi3_eq]
  omega

theorem sort3_swap23 (a b c : ℕ) : lo3 a c b = lo3 a b c ∧ mid3 a c b = mid3 a b c ∧ hi3 a c b = hi3 a b c := by
  simp only [mid3_eq, lo3_eq, hi3_eq]
  omega

theorem sort3_sorted {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : lo3 a b c = a ∧ mid3 a b c = b ∧ hi3 a b c = c := by
  simp only [mid3_eq, lo3_eq, hi3_eq]
  omega

/-! ## Labellings -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over the points other than `i` and `j`. -/
theorem sum_ne_ne {M : Type*} [AddCommGroup M] {i j : ι} (hij : i ≠ j) (G : ι → M) :
    (∑ k, if i ≠ k ∧ j ≠ k then G k else 0) = (∑ k, G k) - G i - G j := by
  have h : ∀ k, (if i ≠ k ∧ j ≠ k then G k else 0)
      = G k - (if k = i then G k else 0) - (if k = j then G k else 0) := by
    intro k
    by_cases h1 : k = i
    · subst h1
      have h2 : ¬ k = j := hij
      simp [h2]
    · by_cases h2 : k = j
      · subst h2
        simp [h1]
      · have h1' : i ≠ k := fun h => h1 h.symm
        have h2' : j ≠ k := fun h => h2 h.symm
        simp [h1, h2, h1', h2']
  simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]

/-- The sum over the points other than `i`. -/
theorem sum_ne {M : Type*} [AddCommGroup M] (i : ι) (G : ι → M) :
    (∑ j, if i ≠ j then G j else 0) = (∑ j, G j) - G i := by
  have h : ∀ j, (if i ≠ j then G j else 0) = G j - (if j = i then G j else 0) := by
    intro j
    by_cases h1 : j = i
    · subst h1
      simp
    · have h1' : i ≠ j := fun h => h1 h.symm
      simp [h1, h1']
  simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]

/-- A labelling of the points by the classes of a certificate. -/
structure Labelling (q : ℕ) (C : Cert) (cls : ι → ℕ) : Prop where
  lt : ∀ i, cls i < q
  card : ∀ x < q, (univ.filter fun k => cls k = x).card = C.n x

namespace Labelling

variable {q : ℕ} {C : Cert} {cls : ι → ℕ}

theorem card_others (L : Labelling q C cls) {i j : ι} (hij : i ≠ j) {x : ℕ} (hx : x < q) :
    ((univ.filter fun k => (i ≠ k ∧ j ≠ k) ∧ cls k = x).card : ℤ)
      = (C.n x : ℤ) - (if x = cls i then 1 else 0) - (if x = cls j then 1 else 0) := by
  have h := sum_ne_ne hij (fun k => if cls k = x then (1 : ℤ) else 0)
  have e : ∀ k, (if (i ≠ k ∧ j ≠ k) ∧ cls k = x then (1 : ℤ) else 0)
      = if i ≠ k ∧ j ≠ k then (if cls k = x then 1 else 0) else 0 := by
    intro k
    by_cases h1 : i ≠ k ∧ j ≠ k
    · simp [h1]
    · simp [h1]
  have hc : ((univ.filter fun k => cls k = x).card : ℤ) = ∑ k, if cls k = x then (1 : ℤ) else 0 := by
    rw [card_filter]
    push_cast
    rfl
  rw [card_filter]
  push_cast
  simp only [e]
  rw [h, ← hc, L.card x hx]
  simp only [eq_comm (a := x)]

theorem mult_add (L : Labelling q C cls) {i j : ι} (hij : i ≠ j) {x : ℕ} (hx : x < q) :
    mult C (cls i) (cls j) x + ((if x = cls i then 1 else 0) + (if x = cls j then 1 else 0)) = C.n x := by
  have h := L.card_others hij hx
  have h0 : (0 : ℤ) ≤ ((univ.filter fun k => (i ≠ k ∧ j ≠ k) ∧ cls k = x).card : ℤ) := Int.natCast_nonneg _
  rw [mult_eq]
  split_ifs at h ⊢ <;> omega

/-- The multiplicity is the number of the further points of a class. -/
theorem mult_card (L : Labelling q C cls) {i j : ι} (hij : i ≠ j) {x : ℕ} (hx : x < q) :
    mult C (cls i) (cls j) x = (univ.filter fun k => (i ≠ k ∧ j ≠ k) ∧ cls k = x).card := by
  have h := L.card_others hij hx
  have h2 := L.mult_add hij hx
  split_ifs at h h2 <;> omega

theorem mult_pos (L : Labelling q C cls) {i j k : ι} (h : Distinct3 i j k) : 0 < mult C (cls i) (cls j) (cls k) := by
  rw [L.mult_card h.1 (L.lt k)]
  exact card_pos.mpr ⟨k, mem_filter.mpr ⟨mem_univ k, ⟨h.2.1, h.2.2⟩, rfl⟩⟩

/-- A sum over the points other than `i` and `j` of a function of the class is a sum over the classes. -/
theorem sum_others (L : Labelling q C cls) {i j : ι} (hij : i ≠ j) (F : ℕ → ℝ) :
    (∑ k, if i ≠ k ∧ j ≠ k then F (cls k) else 0) = ∑ x ∈ range q, (mult C (cls i) (cls j) x : ℝ) * F x := by
  rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := cls) (t := range q) (fun k _ => mem_range.mpr (L.lt k))]
  refine sum_congr rfl fun x hx => ?_
  have e : ∀ k ∈ (univ.filter fun k => i ≠ k ∧ j ≠ k).filter (fun k => cls k = x), F (cls k) = F x :=
    fun k hk => by rw [(mem_filter.mp hk).2]
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul, filter_filter, L.mult_card hij (mem_range.mp hx)]

omit [DecidableEq ι] in
/-- A sum over the points of a function of the class is a sum over the classes. -/
theorem sum_cls (L : Labelling q C cls) (F : ℕ → ℝ) : ∑ k, F (cls k) = ∑ x ∈ range q, (C.n x : ℝ) * F x := by
  rw [← sum_fiberwise_of_maps_to (g := cls) (t := range q) (fun k _ => mem_range.mpr (L.lt k))]
  refine sum_congr rfl fun x hx => ?_
  have e : ∀ k ∈ univ.filter (fun k => cls k = x), F (cls k) = F x := fun k hk => by rw [(mem_filter.mp hk).2]
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul, L.card x (mem_range.mp hx)]

/-- The same for the points other than `i`. -/
theorem sum_other (L : Labelling q C cls) (i : ι) (F : ℕ → ℝ) :
    (∑ j, if i ≠ j then F (cls j) else 0)
      = ∑ b ∈ range q, ((C.n b : ℝ) - (if b = cls i then 1 else 0)) * F b := by
  rw [sum_ne i (fun j => F (cls j)), L.sum_cls F]
  have e : F (cls i) = ∑ b ∈ range q, (if b = cls i then (1 : ℝ) else 0) * F b := by
    simp [L.lt i]
  rw [e, ← sum_sub_distrib]
  exact sum_congr rfl fun b _ => by ring

/-- **The triples of points by their classes.** The sum of a function of the classes over the triples of
distinct points is a sum over the triples of classes: the triple `(a, b, c)` occurs
`n a * (n b - δ) * mult a b c` times. -/
theorem dsum3_cls (L : Labelling q C cls) (F : ℕ → ℕ → ℕ → ℝ) :
    dsum3 (fun i j k => F (cls i) (cls j) (cls k))
      = ∑ a ∈ range q, ∑ b ∈ range q, ∑ c ∈ range q,
          (C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ) * F a b c := by
  have h1 : ∀ i j, (∑ k, if Distinct3 i j k then F (cls i) (cls j) (cls k) else 0)
      = if i ≠ j then ∑ c ∈ range q, (mult C (cls i) (cls j) c : ℝ) * F (cls i) (cls j) c else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [Distinct3]
    · rw [if_pos hij, ← L.sum_others hij (fun c => F (cls i) (cls j) c)]
      exact sum_congr rfl fun k _ => if_congr ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hij, h.1, h.2⟩⟩ rfl rfl
  have h2 : ∀ i, (∑ j, if i ≠ j then ∑ c ∈ range q, (mult C (cls i) (cls j) c : ℝ) * F (cls i) (cls j) c else 0)
      = ∑ b ∈ range q, ((C.n b : ℝ) - (if b = cls i then 1 else 0))
          * ∑ c ∈ range q, (mult C (cls i) b c : ℝ) * F (cls i) b c :=
    fun i => L.sum_other i (fun b => ∑ c ∈ range q, (mult C (cls i) b c : ℝ) * F (cls i) b c)
  unfold dsum3 sum3
  simp only [h1, h2]
  rw [L.sum_cls (fun a => ∑ b ∈ range q, ((C.n b : ℝ) - (if b = a then 1 else 0))
    * ∑ c ∈ range q, (mult C a b c : ℝ) * F a b c)]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun c _ => by ring

end Labelling

end CAP.Wsos
