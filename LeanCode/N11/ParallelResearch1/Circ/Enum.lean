module

public import N11.ParallelResearch1.Circ.Graph
public import N11.ParallelResearch1.Circ.EnumKernel

/-!
# The enumeration of contact graphs by adding a point: soundness of the check of a level

Let `x` be a configuration of `N` points of the unit sphere of `ℝ³`.

* `Bad x m h`: no `m` points of `x` have the pattern `h`.
* `Open x F c k`: some `k` points of `x` have a pattern of the table `F` (with `c` entries).

`step`: let every pattern of the tables `B m` be bad for `x`, and let every pattern of the table `F` of the level `k`
have an accepted row (`rowOk`). If some `k` points of `x` have a pattern of `F` and `k < N`, then some `k + 1` points
have a pattern of the table `F1`. The proof adds a point of `x` that is not among the `k` points; the set `S` of
the points with inner product at least `-2/25` with it gives an extension of the pattern, and the entry of `S` in
the row says that the extension is a pattern of `F1` with other labels, or that it contains a bad pattern.

`bad_five`: no five points have pairwise inner products at most `-2/25`. (Five vectors of `ℝ³` with pairwise
negative inner products do not exist: four of them are linearly dependent, `∑ c_i v_i = 0`; then
`‖∑ |c_i| v_i‖² ≤ ‖∑ c_i v_i‖² = 0`, and the inner product of `∑ |c_i| v_i` with the fifth vector is negative.)

`rowsOk_sound` turns the theorem of a list of rows into the hypothesis of `step` for its patterns, and
`bad_of_list` turns the theorems of a list of certificates into the hypothesis on a part of a table `B m`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-! ## Bits -/

theorem strict_eq (v : ℕ) (f : ℕ → Bool) : strict v f = f v := rfl

theorem sameB_iff {a b : Bool} : sameB a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [sameB]

theorem tbit_eq_testBit (g i : ℕ) : tbit g i = g.testBit i := by
  unfold tbit
  have h1 : Nat.land (Nat.shiftRight g i) 1 = g / 2 ^ i % 2 := by
    show (g >>> i) &&& 1 = g / 2 ^ i % 2
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (g / 2 ^ i) with e | e <;> rw [e] <;> rfl

theorem pairs_succ (b : ℕ) : pairs (b + 1) = pairs b + b := by
  unfold pairs
  show (b + 1) * b / 2 = b * Nat.pred b / 2 + b
  cases b with
  | zero => rfl
  | succ c =>
    show (c + 1 + 1) * (c + 1) / 2 = (c + 1) * c / 2 + (c + 1)
    have e : (c + 1 + 1) * (c + 1) = (c + 1) * c + 2 * (c + 1) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

theorem pairs_mono {a b : ℕ} (h : a ≤ b) : pairs a ≤ pairs b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [pairs_succ]; omega

theorem pairs_add_lt {a b k : ℕ} (hab : a < b) (hb : b < k) : pairs b + a < pairs k := by
  have h1 : pairs (b + 1) ≤ pairs k := pairs_mono hb
  rw [pairs_succ] at h1
  omega

/-- The bits of an extension below `2 ^ P` are those of `g`. -/
theorem tbit_ext_lo {g S P i : ℕ} (hg : g < 2 ^ P) (hi : i < P) : tbit (g + S * 2 ^ P) i = tbit g i := by
  rw [tbit_eq_testBit, tbit_eq_testBit, show g + S * 2 ^ P = 2 ^ P * S + g by ring,
    Nat.testBit_two_pow_mul_add _ hg, if_pos hi]

/-- The bits of an extension from `2 ^ P` on are those of `S`. -/
theorem tbit_ext_hi {g S P : ℕ} (hg : g < 2 ^ P) (a : ℕ) : tbit (g + S * 2 ^ P) (P + a) = tbit S a := by
  rw [tbit_eq_testBit, tbit_eq_testBit, show g + S * 2 ^ P = 2 ^ P * S + g by ring,
    Nat.testBit_two_pow_mul_add _ hg, if_neg (by omega), Nat.add_sub_cancel_left]

/-- The number whose bit `a < k` says whether `c a` holds. -/
noncomputable def nbCode (c : ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | k + 1 => by classical exact 2 ^ k * (if c k then 1 else 0) + nbCode c k

theorem nbCode_lt (c : ℕ → Prop) : ∀ k, nbCode c k < 2 ^ k
  | 0 => by simp [nbCode]
  | k + 1 => by
    have ih := nbCode_lt c k
    classical
    show 2 ^ k * (if c k then 1 else 0) + nbCode c k < 2 ^ (k + 1)
    have : (if c k then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h2 : 2 ^ k * (if c k then 1 else 0) ≤ 2 ^ k := by
      calc 2 ^ k * (if c k then 1 else 0) ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ this
        _ = 2 ^ k := Nat.mul_one _
    rw [pow_succ]
    omega

theorem nbCode_bit (c : ℕ → Prop) : ∀ k a, a < k → (tbit (nbCode c k) a = true ↔ c a)
  | 0, a, h => absurd h (Nat.not_lt_zero a)
  | k + 1, a, h => by
    classical
    have hlt := nbCode_lt c k
    rw [tbit_eq_testBit]
    show (2 ^ k * (if c k then 1 else 0) + nbCode c k).testBit a = true ↔ c a
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h1 | h1
    · rw [if_pos h1, ← tbit_eq_testBit]
      exact nbCode_bit c k a h1
    · subst h1
      rw [if_neg (lt_irrefl a), Nat.sub_self]
      by_cases hc : c a
      · simp [hc]
      · simp [hc]

/-! ## Embeddings -/

theorem embOk_sound {m h n g s : ℕ} (H : embOk m h n g s = true) :
    (∀ b < m, dig s b < n)
      ∧ ∀ b < m, ∀ a < b, dig s a ≠ dig s b ∧ adjG h a b = adjG g (dig s a) (dig s b) := by
  unfold embOk at H
  rw [allN_iff] at H
  constructor
  · intro b hb
    have hb' := H b hb
    simp only [strict_eq, Bool.and_eq_true] at hb'
    have := hb'.1
    rw [Nat.blt_eq] at this
    exact this
  · intro b hb a ha
    have hb' := H b hb
    simp only [strict_eq, Bool.and_eq_true] at hb'
    have ha' := (allN_iff _ _).mp hb'.2 a ha
    cases hbeq : Nat.beq (dig s a) (dig s b) with
    | true =>
      rw [hbeq] at ha'
      exact absurd ha' (by simp)
    | false =>
      rw [hbeq] at ha'
      refine ⟨fun e => ?_, ?_⟩
      · rw [e, Nat.beq_refl] at hbeq
        exact absurd hbeq (by simp)
      · rw [adjG_lt ha]
        exact sameB_iff.mp ha'

section Config

variable {N : ℕ} {x : Fin N → EuclideanSpace ℝ (Fin 3)}

/-- An embedding of patterns carries points with the larger pattern to points with the smaller one. -/
theorem hasPat_comp {p : ℕ → Fin N} {m h n g s : ℕ} (H : embOk m h n g s = true) (hp : InjOn' p n)
    (hg : HasPat x p n g) :
    InjOn' (fun a => p (dig s a)) m ∧ HasPat x (fun a => p (dig s a)) m h := by
  obtain ⟨hlt, hpair⟩ := embOk_sound H
  have hne : ∀ a b, a < m → b < m → a ≠ b → dig s a ≠ dig s b := by
    intro a b ha hb hab
    rcases Nat.lt_or_gt_of_ne hab with h1 | h1
    · exact (hpair b hb a h1).1
    · exact fun e => (hpair a ha b h1).1 e.symm
  constructor
  · intro a b ha hb e
    by_contra hab
    exact hne a b ha hb hab (hp _ _ (hlt a ha) (hlt b hb) e)
  · intro a b ha hb hab
    have hd := hne a b ha hb hab
    have key : adjG h a b = adjG g (dig s a) (dig s b) := by
      rcases Nat.lt_or_gt_of_ne hab with h1 | h1
      · exact (hpair b hb a h1).2
      · rw [adjG_symm h hab, adjG_symm g hd]
        exact (hpair a ha b h1).2
    rw [key]
    exact hg _ _ (hlt a ha) (hlt b hb) hd

/-! ## The step of the enumeration -/

/-- No `m` points of the configuration have the pattern `h`. -/
def Bad (x : Fin N → EuclideanSpace ℝ (Fin 3)) (m h : ℕ) : Prop :=
  ∀ p : ℕ → Fin N, InjOn' p m → ¬ HasPat x p m h

/-- Some `k` points of the configuration have a pattern of the table `F` with `c` entries. -/
def Open (x : Fin N → EuclideanSpace ℝ (Fin 3)) (F c k : ℕ) : Prop :=
  ∃ j < c, ∃ p : ℕ → Fin N, InjOn' p k ∧ HasPat x p k (tabAt F j)

theorem exists_fresh {k : ℕ} (p : ℕ → Fin N) (hk : k < N) : ∃ i : Fin N, ∀ a < k, p a ≠ i := by
  by_contra hne
  push_neg at hne
  have hsub : (univ : Finset (Fin N)) ⊆ image p (range k) := by
    intro i _
    obtain ⟨a, ha, e⟩ := hne i
    exact mem_image.mpr ⟨a, mem_range.mpr ha, e⟩
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := range k) (f := p)
  rw [card_univ, Fintype.card_fin] at h1
  rw [card_range] at h2
  omega

/-- The pattern of `k` points and a further point: the extension by the set of the points with inner product at
least `-2/25` with the further point. -/
theorem hasPat_extend {p : ℕ → Fin N} {k g : ℕ} (hg : HasPat x p k g) (hlt : g < 2 ^ pairs k) (i0 : Fin N) :
    HasPat x (fun a => if a < k then p a else i0) (k + 1)
      (g + nbCode (fun a => theta ≤ inner ℝ (x (p a)) (x i0)) k * 2 ^ pairs k) := by
  set S := nbCode (fun a => theta ≤ inner ℝ (x (p a)) (x i0)) k with hS
  -- a pair of an old point `a` and the new point
  have hnew : ∀ a, a < k →
      (adjG (g + S * 2 ^ pairs k) a k = true → theta ≤ inner ℝ (x (p a)) (x i0))
        ∧ (adjG (g + S * 2 ^ pairs k) a k = false → inner ℝ (x (p a)) (x i0) ≤ theta) := by
    intro a ha
    rw [adjG_lt ha, tbit_ext_hi hlt]
    have hb := nbCode_bit (fun a => theta ≤ inner ℝ (x (p a)) (x i0)) k a ha
    constructor
    · intro e
      exact hb.mp e
    · intro e
      have : ¬ theta ≤ inner ℝ (x (p a)) (x i0) := fun hc => by
        rw [hb.mpr hc] at e
        exact absurd e (by simp)
      exact le_of_lt (not_le.mp this)
  intro a b ha hb hab
  beta_reduce
  rcases Nat.lt_or_ge a k with hak | hak
  · rcases Nat.lt_or_ge b k with hbk | hbk
    · -- two old points
      have e : adjG (g + S * 2 ^ pairs k) a b = adjG g a b := by
        rcases Nat.lt_or_gt_of_ne hab with h1 | h1
        · rw [adjG_lt h1, adjG_lt h1, tbit_ext_lo hlt (pairs_add_lt h1 hbk)]
        · rw [adjG_symm _ hab, adjG_symm g hab, adjG_lt h1, adjG_lt h1, tbit_ext_lo hlt (pairs_add_lt h1 hak)]
      rw [e, if_pos hak, if_pos hbk]
      exact hg a b hak hbk hab
    · have ebk : b = k := by omega
      subst ebk
      rw [if_pos hak, if_neg (lt_irrefl b)]
      exact hnew a hak
  · have eak : a = k := by omega
    subst eak
    have hbk : b < a := by omega
    rw [if_neg (lt_irrefl a), if_pos hbk, adjG_symm _ hab, real_inner_comm]
    exact hnew b hbk

/-- **The step of the enumeration.** -/
theorem step {k F c F1 c1 : ℕ} {B Bc : List ℕ} (hk : k < N)
    (hbad : ∀ m j, j < nth Bc m → Bad x m (tabAt (nth B m) j))
    (hrows : ∀ i < c, ∃ row, rowOk k (tabAt F i) F1 c1 B Bc row = true)
    (ho : Open x F c k) : Open x F1 c1 (k + 1) := by
  obtain ⟨j, hj, p, hp, hg⟩ := ho
  obtain ⟨row, hrow⟩ := hrows j hj
  unfold rowOk at hrow
  simp only [strict_eq, Bool.and_eq_true] at hrow
  obtain ⟨hlt, hall⟩ := hrow
  rw [Nat.blt_eq] at hlt
  have hlt' : tabAt F j < 2 ^ pairs k := hlt
  obtain ⟨i0, hi0⟩ := exists_fresh p hk
  set S := nbCode (fun a => theta ≤ inner ℝ (x (p a)) (x i0)) k with hS
  have hSlt : S < 2 ^ k := nbCode_lt _ k
  have hent := (allN_iff _ _).mp hall S hSlt
  -- the `k + 1` points and their pattern
  have hp' : InjOn' (fun a => if a < k then p a else i0) (k + 1) := by
    intro a b ha hb e
    beta_reduce at e
    by_cases hak : a < k
    · by_cases hbk : b < k
      · rw [if_pos hak, if_pos hbk] at e
        exact hp a b hak hbk e
      · rw [if_pos hak, if_neg hbk] at e
        exact absurd e (hi0 a hak)
    · by_cases hbk : b < k
      · rw [if_neg hak, if_pos hbk] at e
        exact absurd e.symm (hi0 b hbk)
      · omega
  have hg' := hasPat_extend hg hlt' i0
  rw [← hS] at hg'
  have hg'' : HasPat x (fun a => if a < k then p a else i0) (k + 1)
      (Nat.add (tabAt F j) (Nat.mul S (Nat.pow 2 (pairs k)))) := hg'
  unfold entryOk at hent
  simp only [strict_eq] at hent
  generalize Nat.land (Nat.shiftRight row (Nat.mul 64 S)) 18446744073709551615 = e at hent
  cases hkind : Nat.beq (Nat.land e 1) 0 with
  | true =>
    rw [hkind] at hent
    simp only [cond_true, Bool.and_eq_true] at hent
    obtain ⟨⟨_, hj1⟩, hemb⟩ := hent
    rw [Nat.blt_eq] at hj1
    obtain ⟨hinj, hpat⟩ := hasPat_comp hemb hp' hg''
    exact ⟨entJ e, hj1, _, hinj, hpat⟩
  | false =>
    rw [hkind] at hent
    simp only [cond_false, Bool.and_eq_true] at hent
    obtain ⟨hj1, hemb⟩ := hent
    rw [Nat.blt_eq] at hj1
    obtain ⟨hinj, hpat⟩ := hasPat_comp hemb hp' hg''
    exact absurd hpat (hbad _ _ hj1 _ hinj)

/-- The start of the enumeration: no points, the empty pattern. -/
theorem open_zero (F : ℕ) {c : ℕ} (hc : 0 < c) (hN : 0 < N) : Open x F c 0 :=
  ⟨0, hc, fun _ => ⟨0, hN⟩, fun a _ ha => absurd ha (Nat.not_lt_zero a), fun a _ ha => absurd ha (Nat.not_lt_zero a)⟩

end Config

/-! ## Lists of rows and lists of certificates -/

theorem rowsOk_sound {k F F1 c1 : ℕ} {B Bc : List ℕ} :
    ∀ (rows : List ℕ) (i0 : ℕ), rowsOk k F F1 c1 B Bc rows i0 = true →
      ∀ i, i0 ≤ i → i < i0 + rows.length → ∃ row, rowOk k (tabAt F i) F1 c1 B Bc row = true
  | [], i0, _, i, h1, h2 => by simp at h2; omega
  | row :: rest, i0, h, i, h1, h2 => by
    have h' : ((strict (tabAt F i0) fun g => rowOk k g F1 c1 B Bc row) && rowsOk k F F1 c1 B Bc rest (Nat.succ i0)) = true := h
    rw [Bool.and_eq_true, strict_eq] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e
      exact ⟨row, h'.1⟩
    · refine rowsOk_sound rest (i0 + 1) h'.2 i e ?_
      simp only [List.length_cons] at h2
      omega

/-- `rowsOk_sound` with the end of the range as a number. -/
theorem rowsOk_range {k F F1 c1 : ℕ} {B Bc : List ℕ} (rows : List ℕ) (i0 n : ℕ)
    (h : rowsOk k F F1 c1 B Bc rows i0 = true) (hn : Nat.add i0 rows.length = n) :
    ∀ i, i0 ≤ i → i < n → ∃ row, rowOk k (tabAt F i) F1 c1 B Bc row = true := by
  subst hn
  exact rowsOk_sound rows i0 h

/-- Two parts of a range. -/
theorem range_join {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ i, a ≤ i → i < b → P i) (h2 : ∀ i, b ≤ i → i < c → P i) :
    ∀ i, a ≤ i → i < c → P i := fun i ha hc =>
  (Nat.lt_or_ge i b).elim (h1 i ha) fun hb => h2 i hb hc

/-- The entries `i0, i0 + 1, …` of the table `T` are the numbers of the list. -/
noncomputable def patsAt (T : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih i => Nat.beq (tabAt T i) g && ih (Nat.succ i))

theorem patsAt_sound {T : ℕ} {P : ℕ → Prop} :
    ∀ (l : List ℕ) (i0 : ℕ), patsAt T l i0 = true → (∀ g ∈ l, P g) →
      ∀ i, i0 ≤ i → i < i0 + l.length → P (tabAt T i)
  | [], i0, _, _, i, h1, h2 => by simp at h2; omega
  | g :: rest, i0, h, hP, i, h1, h2 => by
    have h' : (Nat.beq (tabAt T i0) g && patsAt T rest (Nat.succ i0)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e
      rw [Nat.eq_of_beq_eq_true h'.1]
      exact hP g (List.mem_cons_self ..)
    · refine patsAt_sound rest (i0 + 1) h'.2 (fun g' hg' => hP g' (List.mem_cons_of_mem _ hg')) i e ?_
      simp only [List.length_cons] at h2
      omega

/-- `patsAt_sound` with the end of the range as a number. -/
theorem patsAt_range {T : ℕ} {P : ℕ → Prop} (l : List ℕ) (i0 n : ℕ) (h : patsAt T l i0 = true)
    (hn : Nat.add i0 l.length = n) (hP : ∀ g ∈ l, P g) : ∀ i, i0 ≤ i → i < n → P (tabAt T i) := by
  subst hn
  exact patsAt_sound l i0 h hP

theorem all_nil {P : ℕ → Prop} : ∀ g ∈ ([] : List ℕ), P g := fun _ h => absurd h (List.not_mem_nil)

theorem all_cons {P : ℕ → Prop} {a : ℕ} {l : List ℕ} (h : P a) (hl : ∀ g ∈ l, P g) : ∀ g ∈ a :: l, P g := by
  intro g hg
  rcases List.mem_cons.mp hg with e | e
  · rw [e]
    exact h
  · exact hl g e

/-- The hypothesis of `step` on the tables of the bad patterns, from the sizes below the length of the list. -/
theorem bad_cases {P : ℕ → ℕ → Prop} {Bc : List ℕ} (h : ∀ m < Bc.length, ∀ j < nth Bc m, P m j) :
    ∀ m j, j < nth Bc m → P m j := by
  intro m j hj
  rcases Nat.lt_or_ge m Bc.length with hm | hm
  · exact h m hm j hj
  · have e : nth Bc m = 0 := by
      rw [nth_eq]
      simp [List.getElem?_eq_none hm]
    rw [e] at hj
    exact absurd hj (Nat.not_lt_zero j)

/-! ## Five far points -/

/-- Five vectors of `ℝ³` with pairwise negative inner products do not exist. -/
theorem no_five_obtuse (v : Fin 5 → EuclideanSpace ℝ (Fin 3)) (h : ∀ a b, a ≠ b → inner ℝ (v a) (v b) < 0) :
    False := by
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 4 => v i.castSucc) := by
    intro hli
    have h1 := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at h1
    omega
  obtain ⟨g, hg0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hcs : ∀ i j : Fin 4, i ≠ j → inner ℝ (v i.castSucc) (v j.castSucc) < 0 := fun i j hij =>
    h _ _ fun e => hij (Fin.castSucc_injective 4 e)
  -- the squared norm of `∑ |g i| v i` is at most that of `∑ g i v i = 0`
  have e1 : inner ℝ (∑ i, |g i| • v i.castSucc) (∑ j, |g j| • v j.castSucc)
      = ∑ i, ∑ j, |g i| * |g j| * inner ℝ (v i.castSucc) (v j.castSucc) := by
    rw [sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have e2 : inner ℝ (∑ i, g i • v i.castSucc) (∑ j, g j • v j.castSucc)
      = ∑ i, ∑ j, g i * g j * inner ℝ (v i.castSucc) (v j.castSucc) := by
    rw [sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have e3 : inner ℝ (∑ i, g i • v i.castSucc) (∑ j, g j • v j.castSucc) = (0 : ℝ) := by
    rw [hg0, inner_zero_left]
  have hw : inner ℝ (∑ i, |g i| • v i.castSucc) (∑ j, |g j| • v j.castSucc) ≤ (0 : ℝ) := by
    rw [e1, ← e3, e2]
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [abs_mul_abs_self]
    · have hneg := hcs i j hij
      have h2 : g i * g j ≤ |g i| * |g j| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith
  have hw0 : (∑ i, |g i| • v i.castSucc) = 0 :=
    inner_self_eq_zero.mp (le_antisymm hw real_inner_self_nonneg)
  -- the inner product with the fifth vector
  have h5 : inner ℝ (∑ i, |g i| • v i.castSucc) (v (Fin.last 4))
      = ∑ i, |g i| * inner ℝ (v i.castSucc) (v (Fin.last 4)) := by
    rw [sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    simp only [conj_trivial]
  rw [hw0, inner_zero_left] at h5
  have hlast : ∀ i : Fin 4, inner ℝ (v i.castSucc) (v (Fin.last 4)) < 0 := fun i =>
    h _ _ (Fin.castSucc_lt_last i).ne
  have hterm : ∀ i ∈ (univ : Finset (Fin 4)), |g i| * inner ℝ (v i.castSucc) (v (Fin.last 4)) ≤ 0 := fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (hlast i).le
  have hi : |g i0| * inner ℝ (v i0.castSucc) (v (Fin.last 4)) < 0 :=
    mul_neg_of_pos_of_neg (abs_pos.mpr hi0) (hlast i0)
  have hsum : ∑ i, |g i| * inner ℝ (v i.castSucc) (v (Fin.last 4)) < 0 := by
    rw [← add_sum_erase univ _ (mem_univ i0)]
    have := sum_nonpos fun i (hi' : i ∈ univ.erase i0) => hterm i (mem_univ i)
    linarith
  linarith

theorem adjG_zero (a b : ℕ) : adjG 0 a b = false := by
  have ht : ∀ i, tbit 0 i = false := fun i => by
    rw [tbit_eq_testBit, Nat.zero_testBit]
  unfold adjG
  cases Nat.blt a b <;> simp [ht]

/-- **Five far points.** No five points of a configuration have pairwise inner products at most `-2/25`: the
pattern without edges on five vertices is bad. -/
theorem bad_five {N : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin 3)) : Bad x 5 0 := by
  intro p hp hg
  refine no_five_obtuse (fun a : Fin 5 => x (p a)) fun a b hab => ?_
  have hne : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have h := (hg a b a.isLt b.isLt hne).2 (adjG_zero a b)
  have ht : theta < 0 := by unfold theta; norm_num
  linarith

/-! ## The exclusion of a pattern with a rational bound -/

/-- `Excl` with the bound `tp / tq`. -/
def ExclQ (tp tq N k g : ℕ) : Prop := Excl ((tp : ℝ) / tq) N k g

end N11.Circ
