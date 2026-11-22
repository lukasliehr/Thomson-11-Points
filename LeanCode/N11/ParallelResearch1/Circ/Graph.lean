module

public import N11.ParallelResearch1.Circ.Fast
public import N11.ParallelResearch1.Circ.GraphKernel

/-!
# Contact graphs of points of a configuration, and the exclusion of a graph by a certificate

Let `x` be a configuration of `N` points of the unit sphere of `ℝ³`, and let `p : ℕ → Fin N` choose points
`p 0, …, p (k - 1)`, distinct (`InjOn' p k`). These points *have the pattern* `g` (`HasPat x p k g`) if for all
`a ≠ b` below `k` the inner product of `x (p a)` and `x (p b)` is at least `-2/25` when the pair is an edge of `g`
and at most `-2/25` otherwise. (At the inner product `-2/25` both hold; the contact graph of the points, with the
edges of inner product at least `-2/25`, is a pattern of them.)

`excl_of_cert`: let a typed certificate satisfy the check `patOk N k g q C Dm` (its domain is that of the pattern `g`
on `k` labelled points; the other points form one class), and let its theorem bound a quantity `F x` from below by
`τ` for all configurations of its domain (`InSource2`). Then `τ < F x` for every configuration `x` of distinct unit
vectors with all inner products at most `73/100` that has `k` points with the pattern `g`.

`Excl τ N k g`: no configuration of `N` distinct unit vectors with all inner products at most `73/100` and with
Coulomb energy at most `τ` has `k` points with the pattern `g`. `excl_of_rows` proves it from the checks of a
certificate.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-- The threshold of the contact graph. -/
noncomputable def theta : ℝ := -2 / 25

section Pat

variable {N : ℕ}

/-- Distinct unit vectors with all inner products at most `73/100`. -/
structure Sep (x : Fin N → EuclideanSpace ℝ (Fin 3)) : Prop where
  unit : ∀ i, ‖x i‖ = 1
  inj : Function.Injective x
  top : ∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ 73 / 100

/-- The first `k` values of `p` are distinct. -/
def InjOn' (p : ℕ → Fin N) (k : ℕ) : Prop := ∀ a b, a < k → b < k → p a = p b → a = b

/-- The points `p 0, …, p (k - 1)` of the configuration have the pattern `g`. -/
def HasPat (x : Fin N → EuclideanSpace ℝ (Fin 3)) (p : ℕ → Fin N) (k g : ℕ) : Prop :=
  ∀ a b, a < k → b < k → a ≠ b →
    (adjG g a b = true → theta ≤ inner ℝ (x (p a)) (x (p b)))
      ∧ (adjG g a b = false → inner ℝ (x (p a)) (x (p b)) ≤ theta)

theorem adjG_lt {g a b : ℕ} (h : a < b) : adjG g a b = tbit g (pairs b + a) := by
  unfold adjG
  have e : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h
  rw [e]
  rfl

theorem adjG_symm (g : ℕ) {a b : ℕ} (h : a ≠ b) : adjG g a b = adjG g b a := by
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · rw [adjG_lt h1]
    unfold adjG
    have e : Nat.blt b a = false := by
      cases hb : Nat.blt b a with
      | false => rfl
      | true => rw [Nat.blt_eq] at hb; omega
    rw [e]
    rfl
  · rw [adjG_lt h1]
    unfold adjG
    have e : Nat.blt a b = false := by
      cases hb : Nat.blt a b with
      | false => rfl
      | true => rw [Nat.blt_eq] at hb; omega
    rw [e]
    rfl

end Pat

/-! ## The intervals of the check -/

theorem ivalBeq_eq {I J : Ival} (h : ivalBeq I J = true) : I = J := by
  unfold ivalBeq at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  cases I
  cases J
  simp only at h1 h2 h3 h4 h5 h6
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6]

theorem ivEdge_lo : ivEdge.lo = theta := by
  unfold Ival.lo ivEdge theta
  norm_num

theorem ivEdge_hi : ivEdge.hi = 73 / 100 := by
  unfold Ival.hi ivEdge
  norm_num

theorem ivFar_lo : ivFar.lo = -1 := by
  unfold Ival.lo ivFar
  norm_num

theorem ivFar_hi : ivFar.hi = theta := by
  unfold Ival.hi ivFar theta
  norm_num

theorem ivFree_lo : ivFree.lo = -1 := by
  unfold Ival.lo ivFree
  norm_num

theorem ivFree_hi : ivFree.hi = 73 / 100 := by
  unfold Ival.hi ivFree
  norm_num

theorem inner_ge_neg_one {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : (-1 : ℝ) ≤ inner ℝ x y := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at h
  exact (abs_le.mp h).1

/-! ## The labelling of a configuration with `k` chosen points -/

section Label

variable {N : ℕ} (p : ℕ → Fin N) (k : ℕ)

open Classical in
/-- The class of a point: the number of the chosen point, or `k` for a point that is not chosen. -/
noncomputable def clsOf (i : Fin N) : ℕ := if h : ∃ a, a < k ∧ p a = i then Nat.find h else k

variable {p k}

theorem clsOf_chosen (hp : InjOn' p k) {a : ℕ} (ha : a < k) : clsOf p k (p a) = a := by
  classical
  have h : ∃ b, b < k ∧ p b = p a := ⟨a, ha, rfl⟩
  unfold clsOf
  rw [dif_pos h]
  have hs := Nat.find_spec h
  exact hp _ _ hs.1 ha hs.2

theorem clsOf_le (i : Fin N) : clsOf p k i ≤ k := by
  classical
  unfold clsOf
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem clsOf_lt {i : Fin N} (h : clsOf p k i < k) : p (clsOf p k i) = i := by
  classical
  unfold clsOf at h ⊢
  split_ifs at h ⊢ with h'
  · exact (Nat.find_spec h').2
  · omega

theorem clsOf_eq_iff (hp : InjOn' p k) {i : Fin N} {c : ℕ} (hc : c < k) : clsOf p k i = c ↔ i = p c := by
  constructor
  · intro h
    have h' : clsOf p k i < k := by omega
    have := clsOf_lt h'
    rw [h] at this
    exact this.symm
  · intro h
    rw [h]
    exact clsOf_chosen hp hc

/-- The labelling by the chosen points is a labelling of a certificate with `k` classes of one point, one class
of the further points and empty classes above. -/
theorem labelling_of (hp : InjOn' p k) {q : ℕ} {C : Cert} (hq : k < q) (h1 : ∀ a < k, C.n a = 1)
    (hk : C.n k + k = N) (h0 : ∀ c, k < c → c < q → C.n c = 0) : Labelling q C (clsOf p k) := by
  classical
  have hfil : ∀ c < k, (univ.filter fun i : Fin N => clsOf p k i = c) = {p c} := by
    intro c hc
    ext i
    rw [mem_filter, mem_singleton, clsOf_eq_iff hp hc]
    simp
  refine ⟨fun i => by have := clsOf_le (p := p) (k := k) i; omega, ?_⟩
  intro c hc
  rcases Nat.lt_or_ge c k with hck | hck
  · rw [hfil c hck, card_singleton, h1 c hck]
  · rcases Nat.eq_or_lt_of_le hck with e | e
    · subst e
      -- the points that are not chosen: all points minus one for each class below `k`
      have htot := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin N))) (t := range (k + 1)) (f := clsOf p k)
        (fun i _ => mem_coe.mpr (mem_range.mpr (Nat.lt_succ_of_le (clsOf_le i))))
      rw [card_univ, Fintype.card_fin, sum_range_succ] at htot
      have hsum : ∑ c ∈ range k, (filter (fun i : Fin N => clsOf p k i = c) univ).card = k := by
        rw [sum_congr rfl fun c hc => by rw [hfil c (mem_range.mp hc), card_singleton]]
        simp
      rw [hsum] at htot
      omega
    · rw [h0 c e hc, card_eq_zero]
      ext i
      have := clsOf_le (p := p) (k := k) i
      simp
      omega

end Label

/-! ## The exclusion of a pattern -/

theorem patOk_sound {N k g q : ℕ} {C : Cert} {Dm : Dom} (h : patOk N k g q C Dm = true) :
    k < q ∧ C.n k + k = N ∧ (∀ c, k < c → c < q → C.n c = 0) ∧ (∀ a < k, C.n a = 1)
      ∧ (∀ b < k, ∀ a < b, Dm.iv a b = if tbit g (pairs b + a) = true then ivEdge else ivFar)
      ∧ (∀ a < k, C.n k = 0 ∨ Dm.iv a k = ivFree) ∧ (C.n k ≤ 1 ∨ Dm.iv k k = ivFree) ∧ Dm.cuts = [] := by
  unfold patOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hq, hk⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨by rw [Nat.blt_eq] at hq; exact hq, Nat.eq_of_beq_eq_true hk, ?_,
    fun a ha => Nat.eq_of_beq_eq_true ((allN_iff _ _).mp h1 a ha), ?_, ?_, ?_, List.isEmpty_iff.mp h5⟩
  · intro c hkc hc
    have e := (allN_iff _ _).mp h0 c hc
    rw [Bool.or_eq_true] at e
    rcases e with e | e
    · rw [Nat.ble_eq] at e
      omega
    · exact Nat.eq_of_beq_eq_true e
  · intro b hb a ha
    have e := ivalBeq_eq ((allN_iff _ _).mp ((allN_iff _ _).mp h2 b hb) a ha)
    rw [e]
    cases tbit g (Nat.add (pairs b) a) <;> rfl
  · intro a ha
    have e := (allN_iff _ _).mp h3 a ha
    rw [Bool.or_eq_true] at e
    rcases e with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (ivalBeq_eq e)
  · rw [Bool.or_eq_true] at h4
    rcases h4 with e | e
    · left
      rw [Nat.ble_eq] at e
      exact e
    · exact Or.inr (ivalBeq_eq e)

/-- **The exclusion of a pattern by a certificate.** -/
theorem excl_of_cert {N k g q : ℕ} {C : Cert} {Dm : Dom} {F : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} {τ : ℝ}
    (hpat : patOk N k g q C Dm = true)
    (hF : ∀ {cls : Fin N → ℕ} {x : Fin N → EuclideanSpace ℝ (Fin 3)}, InSource2 q C Dm cls x → τ < F x)
    {x : Fin N → EuclideanSpace ℝ (Fin 3)} (hx : Sep x) {p : ℕ → Fin N} (hp : InjOn' p k) (hg : HasPat x p k g) :
    τ < F x := by
  obtain ⟨hq, hk, h0, h1, h2, h3, h4, hcuts⟩ := patOk_sound hpat
  have L := labelling_of hp hq h1 hk h0
  refine hF (cls := clsOf p k) ⟨L, hx.unit, hx.inj, ?_, ?_⟩
  · intro i j hij hle
    have hlow := inner_ge_neg_one (hx.unit i) (hx.unit j)
    have htop := hx.top i j hij
    rcases Nat.lt_or_ge (clsOf p k j) k with hj | hj
    · -- both points are chosen
      have hi : clsOf p k i < k := lt_of_le_of_lt hle hj
      have ei := clsOf_lt hi
      have ej := clsOf_lt hj
      have hne : clsOf p k i ≠ clsOf p k j := fun e => hij (by rw [← ei, ← ej, e])
      have hlt : clsOf p k i < clsOf p k j := lt_of_le_of_ne hle hne
      have hpair := hg _ _ hi hj hne
      rw [ei, ej, adjG_lt hlt] at hpair
      rw [h2 _ hj _ hlt]
      cases hb : tbit g (pairs (clsOf p k j) + clsOf p k i) with
      | true =>
        rw [if_pos rfl, ivEdge_lo, ivEdge_hi]
        exact ⟨hpair.1 hb, htop⟩
      | false =>
        rw [if_neg (by simp), ivFar_lo, ivFar_hi]
        exact ⟨hlow, hpair.2 hb⟩
    · have ej : clsOf p k j = k := le_antisymm (clsOf_le j) hj
      have hnk : 0 < C.n k := by
        rw [← L.card k hq]
        exact card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_univ j, ej⟩⟩
      rcases Nat.lt_or_ge (clsOf p k i) k with hi | hi
      · rcases h3 _ hi with e | e
        · omega
        · rw [ej, e, ivFree_lo, ivFree_hi]
          exact ⟨hlow, htop⟩
      · have ei : clsOf p k i = k := le_antisymm (clsOf_le i) hi
        have hnk2 : 1 < C.n k := by
          rw [← L.card k hq]
          exact one_lt_card.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, ei⟩, j, mem_filter.mpr ⟨mem_univ j, ej⟩, hij⟩
        rcases h4 with e | e
        · omega
        · rw [ei, ej, e, ivFree_lo, ivFree_hi]
          exact ⟨hlow, htop⟩
  · intro i j l _ _ _ g' hg'
    rw [hcuts] at hg'
    simp [findCuts] at hg'

/-! ## The Coulomb energy and the exclusion of a pattern below an energy -/

/-- The Coulomb energy of a configuration. -/
noncomputable def energy {N : ℕ} (x : Fin N → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖

/-- No configuration of `N` distinct unit vectors with all inner products at most `73/100` and with energy at most
`τ` has `k` points with the pattern `g`. -/
def Excl (τ : ℝ) (N k g : ℕ) : Prop :=
  ∀ x : Fin N → EuclideanSpace ℝ (Fin 3), Sep x → energy x ≤ τ → ∀ p : ℕ → Fin N, InjOn' p k → ¬ HasPat x p k g

/-- **The exclusion of a pattern from the checks of a certificate.** -/
theorem excl_of_rows {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq N k g : ℕ}
    {l : List (List Sign2)} (H : CertHolds2 P Q C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant2 P C Dm sP (signOfRows l)) (hpen : pensZeroR l = true)
    (hb : boundOk2 P C xs sP M tp tq = true) (hpat : patOk N k g P.q C Dm = true) :
    Excl ((tp : ℝ) / tq) N k g := by
  intro x hx hE p hp hg
  have h := excl_of_cert (F := energy) (τ := (tp : ℝ) / tq) hpat
    (fun {cls} {x} hS => coulomb2_gt_rows H hdom hmin hpen hb hS) hx hp hg
  exact absurd hE (not_le.mpr h)

end N11.Circ
