module

public import N11.ParallelResearch1.Circ.Enum
public import N11.ParallelResearch1.Circ.CellKernel

/-!
# Cells of labelled points: covers, the theorem of a certificate on a cell, the penalty

Let `x` be a configuration of points of the unit sphere of `ℝ³` and let `p` number `N` of them. `InCell N iv x p`: the
inner product of the points `p a`, `p b` lies in the interval `iv a b`, for all `a < b < N`.

* `inCell_of_hasPat`: points with the pattern `g` lie in the cell `patCell g`.
* `peel_cover`: a cell `c` is covered by a box `b` and the slabs `slabIv c b T u v side` of the sides that are not
  empty. (Take a pair outside the box whose position in the order `T` is least.)
* `halve_cover`: a cell is covered by its two halves along a pair.
* `cell_of_rows`: the Coulomb energy exceeds the target on the cell of a certificate with `N` classes of one point.
* `penIs_val`, `conf_of_rows`: for a certificate with the polynomials `pen = (cn / cd) (t - τ)²`, the energy minus
  `(cn / cd) ∑ (t_ij - τ_ij)²` exceeds the target on its cell.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-! ## Truth values -/

theorem nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem nat_blt_true {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem nat_blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b with
  | false => rfl
  | true =>
    rw [Nat.blt_eq] at hb
    exact absurd hb h

theorem pair_beq_false {a b u v : ℕ} (h : ¬(a = u ∧ b = v)) : (Nat.beq a u && Nat.beq b v) = false := by
  rcases not_and_or.mp h with h1 | h1
  · rw [nat_beq_false h1]
    rfl
  · rw [nat_beq_false h1, Bool.and_false]

/-! ## Intervals -/

theorem below_lo (I J : Ival) : (below I J).lo = I.lo := rfl

theorem below_hi (I J : Ival) : (below I J).hi = J.lo := rfl

theorem above_lo (I J : Ival) : (above I J).lo = J.hi := rfl

theorem above_hi (I J : Ival) : (above I J).hi = I.hi := rfl

theorem loBeq_lo {I J : Ival} (h : loBeq I J = true) : I.lo = J.lo := by
  unfold loBeq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Ival.lo
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]

theorem hiBeq_hi {I J : Ival} (h : hiBeq I J = true) : I.hi = J.hi := by
  unfold hiBeq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Ival.hi
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]

theorem loHiBeq_eq {I J : Ival} (h : loHiBeq I J = true) : I.lo = J.hi := by
  unfold loHiBeq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold Ival.lo Ival.hi
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]

theorem ivsBeq_sound {N : ℕ} {f g : ℕ → ℕ → Ival} (h : ivsBeq N f g = true) {a b : ℕ} (hab : a < b) (hb : b < N) :
    f a b = g a b :=
  ivalBeq_eq ((allN_iff _ _).mp ((allN_iff _ _).mp h b hb) a hab)

theorem qle_sound {p1 n1 d1 p2 n2 d2 : ℕ} (h : qle p1 n1 d1 p2 n2 d2 = true) (h1 : 0 < d1) (h2 : 0 < d2) :
    ((p1 : ℝ) - n1) / d1 ≤ ((p2 : ℝ) - n2) / d2 := by
  unfold qle at h
  rw [Nat.ble_eq] at h
  have h' : p1 * d2 + n2 * d1 ≤ p2 * d1 + n1 * d2 := h
  have hr : (p1 : ℝ) * d2 + n2 * d1 ≤ p2 * d1 + n1 * d2 := by exact_mod_cast h'
  have hd1 : (0 : ℝ) < d1 := by exact_mod_cast h1
  have hd2 : (0 : ℝ) < d2 := by exact_mod_cast h2
  rw [div_le_div_iff₀ hd1 hd2]
  linarith

theorem posDen_pos {I : Ival} (h : posDen I = true) : 0 < I.ld ∧ 0 < I.hd := by
  unfold posDen at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
  exact h

theorem subIv_sound {I J : Ival} (h : subIv I J = true) : J.lo ≤ I.lo ∧ I.hi ≤ J.hi := by
  unfold subIv at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hI, hJ⟩, h1⟩, h2⟩ := h
  obtain ⟨hI1, hI2⟩ := posDen_pos hI
  obtain ⟨hJ1, hJ2⟩ := posDen_pos hJ
  exact ⟨qle_sound h1 hJ1 hI1, qle_sound h2 hI2 hJ2⟩

/-! ## Cells -/

section Cells

variable {M : ℕ} {x : Fin M → EuclideanSpace ℝ (Fin 3)} {p : ℕ → Fin M}

/-- The inner products of the points `p 0, …, p (N - 1)` lie in the intervals of the cell. -/
def InCell (N : ℕ) (iv : ℕ → ℕ → Ival) (x : Fin M → EuclideanSpace ℝ (Fin 3)) (p : ℕ → Fin M) : Prop :=
  ∀ a b, a < b → b < N →
    (iv a b).lo ≤ inner ℝ (x (p a)) (x (p b)) ∧ inner ℝ (x (p a)) (x (p b)) ≤ (iv a b).hi

/-- Cells with the same intervals have the same points. -/
theorem inCell_congr {N : ℕ} {f g : ℕ → ℕ → Ival} (h : ivsBeq N f g = true) (hg : InCell N g x p) :
    InCell N f x p := by
  intro a b hab hb
  rw [ivsBeq_sound h hab hb]
  exact hg a b hab hb

theorem inCell_congr' {N : ℕ} {f g : ℕ → ℕ → Ival} (h : ivsBeq N f g = true) (hf : InCell N f x p) :
    InCell N g x p := by
  intro a b hab hb
  rw [← ivsBeq_sound h hab hb]
  exact hf a b hab hb

/-- A cell whose intervals are contained in those of another cell has its points in the other cell. -/
theorem inCell_mono {N : ℕ} {f g : ℕ → ℕ → Ival} (h : ivsSub N f g = true) (hf : InCell N f x p) :
    InCell N g x p := by
  intro a b hab hb
  have hs := subIv_sound ((allN_iff _ _).mp ((allN_iff _ _).mp h b hb) a hab)
  have := hf a b hab hb
  exact ⟨le_trans hs.1 this.1, le_trans this.2 hs.2⟩

/-- Points with a pattern lie in the cell of the pattern. -/
theorem inCell_of_hasPat {N g : ℕ} (hx : Sep x) (hp : InjOn' p N) (hg : HasPat x p N g) :
    InCell N (patCell g) x p := by
  intro a b hab hb
  have ha : a < N := lt_trans hab hb
  have hne : a ≠ b := ne_of_lt hab
  have hpne : p a ≠ p b := fun e => hne (hp a b ha hb e)
  have hlow := inner_ge_neg_one (hx.unit (p a)) (hx.unit (p b))
  have htop := hx.top _ _ hpne
  have hpair := hg a b ha hb hne
  rw [adjG_lt hab] at hpair
  cases hbit : tbit g (pairs b + a) with
  | true =>
    have e : patCell g a b = ivEdge := by
      show cond (tbit g (pairs b + a)) ivEdge ivFar = ivEdge
      rw [hbit]
      rfl
    rw [e, ivEdge_lo, ivEdge_hi]
    exact ⟨hpair.1 hbit, htop⟩
  | false =>
    have e : patCell g a b = ivFar := by
      show cond (tbit g (pairs b + a)) ivEdge ivFar = ivFar
      rw [hbit]
      rfl
    rw [e, ivFar_lo, ivFar_hi]
    exact ⟨hlow, hpair.2 hbit⟩

/-! ## The peel of a cell around a box -/

theorem slabIv_before {c b : ℕ → ℕ → Ival} {T u v side a b' : ℕ} (h : posAt T a b' < posAt T u v) :
    slabIv c b T u v side a b' = b a b' := by
  show cond (Nat.blt (posAt T a b') (posAt T u v)) _ _ = _
  rw [nat_blt_true h]
  rfl

theorem slabIv_self (c b : ℕ → ℕ → Ival) (T u v side : ℕ) :
    slabIv c b T u v side u v = cond (Nat.beq side 0) (below (c u v) (b u v)) (above (c u v) (b u v)) := by
  show cond (Nat.blt (posAt T u v) (posAt T u v)) _ (cond (Nat.beq u u && Nat.beq v v) _ _) = _
  rw [nat_blt_false (lt_irrefl _), Nat.beq_refl, Nat.beq_refl]
  rfl

theorem slabIv_other {c b : ℕ → ℕ → Ival} {T u v side a b' : ℕ} (h : ¬ posAt T a b' < posAt T u v)
    (hne : ¬(a = u ∧ b' = v)) : slabIv c b T u v side a b' = c a b' := by
  show cond (Nat.blt (posAt T a b') (posAt T u v)) _ (cond (Nat.beq a u && Nat.beq b' v) _ _) = _
  rw [nat_blt_false h, pair_beq_false hne]
  rfl

theorem sideOut_sound {c b : ℕ → ℕ → Ival} {u v side : ℕ} (h : sideOut c b u v side = true) :
    (side = 0 → (b u v).lo ≤ (c u v).lo) ∧ (side ≠ 0 → (c u v).hi ≤ (b u v).hi) := by
  unfold sideOut at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, hb⟩, h1⟩ := h
  obtain ⟨hc1, hc2⟩ := posDen_pos hc
  obtain ⟨hb1, hb2⟩ := posDen_pos hb
  constructor
  · intro e
    subst e
    exact qle_sound h1 hb1 hc1
  · intro e
    rw [nat_beq_false e] at h1
    exact qle_sound h1 hc2 hb2

/-- **The peel of a cell.** A cell is covered by a box and the slabs of the sides that are not empty. -/
theorem peel_cover {N T : ℕ} {c b : ℕ → ℕ → Ival} {G : Prop} (hc : InCell N c x p) (hbox : InCell N b x p → G)
    (hs : ∀ u v, u < v → v < N → ∀ side, side < 2 →
      sideOut c b u v side = true ∨ (InCell N (slabIv c b T u v side) x p → G)) : G := by
  by_cases hin : InCell N b x p
  · exact hbox hin
  -- a pair outside the box whose position is least
  have hex : ∃ n, ∃ u v, u < v ∧ v < N ∧ posAt T u v = n
      ∧ ¬((b u v).lo ≤ inner ℝ (x (p u)) (x (p v)) ∧ inner ℝ (x (p u)) (x (p v)) ≤ (b u v).hi) := by
    by_contra hno
    apply hin
    intro a b' hab hb'
    by_contra hv
    exact hno ⟨posAt T a b', a, b', hab, hb', rfl, hv⟩
  classical
  obtain ⟨u, v, huv, hv, hpos, hviol⟩ := Nat.find_spec hex
  have hmin : ∀ a b', a < b' → b' < N → posAt T a b' < posAt T u v →
      ((b a b').lo ≤ inner ℝ (x (p a)) (x (p b')) ∧ inner ℝ (x (p a)) (x (p b')) ≤ (b a b').hi) := by
    intro a b' hab hb' hlt
    by_contra hv'
    rw [hpos] at hlt
    exact Nat.find_min hex hlt ⟨a, b', hab, hb', rfl, hv'⟩
  have hcuv := hc u v huv hv
  -- the points lie in the slab of this pair on the side where the box is left
  have hslab : ∀ side, (cond (Nat.beq side 0) (below (c u v) (b u v)) (above (c u v) (b u v))).lo
        ≤ inner ℝ (x (p u)) (x (p v))
      → inner ℝ (x (p u)) (x (p v)) ≤ (cond (Nat.beq side 0) (below (c u v) (b u v)) (above (c u v) (b u v))).hi
      → InCell N (slabIv c b T u v side) x p := by
    intro side h1 h2 a b' hab hb'
    by_cases hlt : posAt T a b' < posAt T u v
    · rw [slabIv_before hlt]
      exact hmin a b' hab hb' hlt
    · by_cases hpair : a = u ∧ b' = v
      · obtain ⟨rfl, rfl⟩ := hpair
        rw [slabIv_self]
        exact ⟨h1, h2⟩
      · rw [slabIv_other hlt hpair]
        exact hc a b' hab hb'
  rcases lt_or_ge (inner ℝ (x (p u)) (x (p v))) (b u v).lo with hlo | hlo
  · rcases hs u v huv hv 0 (by norm_num) with he | hsl
    · have e : (b u v).lo ≤ (c u v).lo := (sideOut_sound he).1 rfl
      linarith [hcuv.1]
    · exact hsl (hslab 0 hcuv.1 hlo.le)
  · have hhi : (b u v).hi < inner ℝ (x (p u)) (x (p v)) := by
      by_contra hno
      exact hviol ⟨hlo, not_lt.mp hno⟩
    rcases hs u v huv hv 1 (by norm_num) with he | hsl
    · have e : (c u v).hi ≤ (b u v).hi := (sideOut_sound he).2 (by norm_num)
      linarith [hcuv.2]
    · exact hsl (hslab 1 hhi.le hcuv.2)

/-- **The halves of a cell.** -/
theorem halve_cover {N u v : ℕ} {s da db : ℕ → ℕ → Ival} (h : halfOk N s da db u v = true) (huv : u < v)
    (hv : v < N) (hs : InCell N s x p) : InCell N da x p ∨ InCell N db x p := by
  have hall : ∀ a b', a < b' → b' < N →
      (cond (Nat.beq a u && Nat.beq b' v)
        (loBeq (da a b') (s a b') && hiBeq (db a b') (s a b') && loHiBeq (db a b') (da a b'))
        (ivalBeq (da a b') (s a b') && ivalBeq (db a b') (s a b'))) = true :=
    fun a b' hab hb' => (allN_iff _ _).mp ((allN_iff _ _).mp h b' hb') a hab
  have huv' := hall u v huv hv
  rw [Nat.beq_refl, Nat.beq_refl] at huv'
  simp only [Bool.and_self, cond_true, Bool.and_eq_true] at huv'
  obtain ⟨⟨h1, h2⟩, h3⟩ := huv'
  have hother : ∀ a b', a < b' → b' < N → ¬(a = u ∧ b' = v) → da a b' = s a b' ∧ db a b' = s a b' := by
    intro a b' hab hb' hne
    have e := hall a b' hab hb'
    rw [pair_beq_false hne] at e
    simp only [cond_false, Bool.and_eq_true] at e
    exact ⟨ivalBeq_eq e.1, ivalBeq_eq e.2⟩
  have hsuv := hs u v huv hv
  rcases le_or_gt (inner ℝ (x (p u)) (x (p v))) (da u v).hi with hle | hgt
  · left
    intro a b' hab hb'
    by_cases hpair : a = u ∧ b' = v
    · obtain ⟨rfl, rfl⟩ := hpair
      rw [loBeq_lo h1]
      exact ⟨hsuv.1, hle⟩
    · rw [(hother a b' hab hb' hpair).1]
      exact hs a b' hab hb'
  · right
    intro a b' hab hb'
    by_cases hpair : a = u ∧ b' = v
    · obtain ⟨rfl, rfl⟩ := hpair
      rw [loHiBeq_eq h3, hiBeq_hi h2]
      exact ⟨hgt.le, hsuv.2⟩
    · rw [(hother a b' hab hb' hpair).2]
      exact hs a b' hab hb'

/-- **A cell covered by two cells along a pair.** -/
theorem halfSub_cover {N u v : ℕ} {s da db : ℕ → ℕ → Ival} (h : halfSub N s da db u v = true) (huv : u < v)
    (hv : v < N) (hs : InCell N s x p) : InCell N da x p ∨ InCell N db x p := by
  have hall : ∀ a b', a < b' → b' < N →
      (cond (Nat.beq a u && Nat.beq b' v)
        (posDen (s a b') && posDen (da a b') && posDen (db a b')
          && qle (da a b').lp (da a b').ln (da a b').ld (s a b').lp (s a b').ln (s a b').ld
          && qle (s a b').hp (s a b').hn (s a b').hd (db a b').hp (db a b').hn (db a b').hd
          && qle (db a b').lp (db a b').ln (db a b').ld (da a b').hp (da a b').hn (da a b').hd)
        (subIv (s a b') (da a b') && subIv (s a b') (db a b'))) = true :=
    fun a b' hab hb' => (allN_iff _ _).mp ((allN_iff _ _).mp h b' hb') a hab
  have huv' := hall u v huv hv
  rw [Nat.beq_refl, Nat.beq_refl] at huv'
  simp only [Bool.and_self, cond_true, Bool.and_eq_true] at huv'
  obtain ⟨⟨⟨⟨⟨hps, hpa⟩, hpb⟩, h1⟩, h2⟩, h3⟩ := huv'
  obtain ⟨hs1, hs2⟩ := posDen_pos hps
  obtain ⟨ha1, ha2⟩ := posDen_pos hpa
  obtain ⟨hb1, hb2⟩ := posDen_pos hpb
  have e1 : (da u v).lo ≤ (s u v).lo := qle_sound h1 ha1 hs1
  have e2 : (s u v).hi ≤ (db u v).hi := qle_sound h2 hs2 hb2
  have e3 : (db u v).lo ≤ (da u v).hi := qle_sound h3 hb1 ha2
  have hother : ∀ a b', a < b' → b' < N → ¬(a = u ∧ b' = v) →
      ((da a b').lo ≤ (s a b').lo ∧ (s a b').hi ≤ (da a b').hi) ∧ ((db a b').lo ≤ (s a b').lo ∧ (s a b').hi ≤ (db a b').hi) := by
    intro a b' hab hb' hne
    have e := hall a b' hab hb'
    rw [pair_beq_false hne] at e
    simp only [cond_false, Bool.and_eq_true] at e
    exact ⟨subIv_sound e.1, subIv_sound e.2⟩
  have hsuv := hs u v huv hv
  rcases le_or_gt (inner ℝ (x (p u)) (x (p v))) (da u v).hi with hle | hgt
  · left
    intro a b' hab hb'
    by_cases hpair : a = u ∧ b' = v
    · obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨le_trans e1 hsuv.1, hle⟩
    · have ho := (hother a b' hab hb' hpair).1
      have := hs a b' hab hb'
      exact ⟨le_trans ho.1 this.1, le_trans this.2 ho.2⟩
  · right
    intro a b' hab hb'
    by_cases hpair : a = u ∧ b' = v
    · obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨le_trans e3 hgt.le, le_trans hsuv.2 e2⟩
    · have ho := (hother a b' hab hb' hpair).2
      have := hs a b' hab hb'
      exact ⟨le_trans ho.1 this.1, le_trans this.2 ho.2⟩

end Cells

/-! ## Statements for all pairs and both sides -/

theorem forall_pairs {N : ℕ} {P : ℕ → ℕ → Prop} (h : ∀ v < N, ∀ u < v, P u v) : ∀ u v, u < v → v < N → P u v :=
  fun u v huv hv => h v hv u huv

theorem forall_lt_list {P : ℕ → Prop} (n : ℕ) (l : List ℕ) (hl : List.range n = l) (h : ∀ m ∈ l, P m) :
    ∀ m < n, P m := fun m hm => h m (hl ▸ List.mem_range.mpr hm)

theorem side2 {Q : ℕ → Prop} (h0 : Q 0) (h1 : Q 1) : ∀ side, side < 2 → Q side := by
  intro side hs
  interval_cases side
  · exact h0
  · exact h1

/-! ## The theorem of a certificate on a cell -/

/-- The Coulomb energy exceeds `tp / tq`. -/
def EnergyGt {N : ℕ} (tp tq : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin 3)) : Prop := (tp : ℝ) / tq < energy x

theorem onesOk_sound {N q : ℕ} {C : Cert} {Dm : Dom} (h : onesOk N q C Dm = true) :
    N < q ∧ (∀ a < N, C.n a = 1) ∧ (∀ c, N ≤ c → c < q → C.n c = 0) ∧ Dm.cuts = [] := by
  unfold onesOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hq, h1⟩, h0⟩, hc⟩ := h
  rw [Nat.blt_eq] at hq
  refine ⟨hq, fun a ha => Nat.eq_of_beq_eq_true ((allN_iff _ _).mp h1 a ha), ?_, List.isEmpty_iff.mp hc⟩
  intro c hNc hc'
  have e := (allN_iff _ _).mp h0 c hc'
  rw [Bool.or_eq_true] at e
  rcases e with e | e
  · rw [Nat.blt_eq] at e
    omega
  · exact Nat.eq_of_beq_eq_true e

section Source

variable {N : ℕ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p : ℕ → Fin N}

/-- The classes of the points of a configuration all of whose points are numbered. -/
theorem clsOf_lt_all {q : ℕ} {C : Cert} (L : Labelling q C (clsOf p N)) (hq : N < q) (h0 : C.n N = 0) (i : Fin N) :
    clsOf p N i < N := by
  rcases Nat.lt_or_ge (clsOf p N i) N with h | h
  · exact h
  · have e : clsOf p N i = N := le_antisymm (clsOf_le i) h
    have hc := L.card N hq
    rw [h0, card_eq_zero] at hc
    have : i ∈ univ.filter fun k => clsOf p N k = N := mem_filter.mpr ⟨mem_univ i, e⟩
    rw [hc] at this
    exact absurd this (notMem_empty i)

/-- A configuration in the cell of a certificate with `N` classes of one point is in its domain. -/
theorem inSource2_of_cell {q : ℕ} {C : Cert} {Dm : Dom} (h : onesOk N q C Dm = true) (hx : Sep x) (hp : InjOn' p N)
    (hin : InCell N Dm.iv x p) : InSource2 q C Dm (clsOf p N) x := by
  obtain ⟨hq, h1, h0, hcuts⟩ := onesOk_sound h
  have hN0 : C.n N = 0 := h0 N le_rfl hq
  have L := labelling_of hp hq h1 (by rw [hN0, Nat.zero_add]) (fun c hc hc' => h0 c hc.le hc')
  have hlt := clsOf_lt_all L hq hN0
  refine ⟨L, hx.unit, hx.inj, ?_, ?_⟩
  · intro i j hij hle
    have ei := clsOf_lt (hlt i)
    have ej := clsOf_lt (hlt j)
    have hne : clsOf p N i ≠ clsOf p N j := fun e => hij (by rw [← ei, ← ej, e])
    have hl : clsOf p N i < clsOf p N j := lt_of_le_of_ne hle hne
    have := hin _ _ hl (hlt j)
    rw [ei, ej] at this
    exact this
  · intro i j l _ _ _ g' hg'
    rw [hcuts] at hg'
    simp [findCuts] at hg'

/-- **The energy on the cell of a certificate.** -/
theorem cell_of_rows {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq : ℕ}
    {l : List (List Sign2)} (H : CertHolds2 P Q C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant2 P C Dm sP (signOfRows l)) (hpen : pensZeroR l = true)
    (hb : boundOk2 P C xs sP M tp tq = true) (hones : onesOk N P.q C Dm = true) (hx : Sep x) (hp : InjOn' p N)
    (hin : InCell N Dm.iv x p) : EnergyGt tp tq x :=
  coulomb2_gt_rows H hdom hmin hpen hb (inSource2_of_cell hones hx hp hin)

end Source

/-! ## The penalty -/

/-- The centre of the pair `a < b` in a table of centres with `tb` binary places. -/
noncomputable def tauV (T tb a b : ℕ) : ℝ := ((tauP T a b : ℝ) - (tauN T a b : ℝ)) / 2 ^ tb

theorem penIs_val {cn cd tb tp tn sP : ℕ} {S : Sign2} (h : penIs cn cd tb tp tn sP S = true) (t : ℝ) :
    S.pen.val (2 ^ sP * (S.sc : ℝ)) t = (cn : ℝ) / cd * (t - ((tp : ℝ) - tn) / 2 ^ tb) ^ 2 := by
  unfold penIs at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcd, hsc⟩, ht0⟩, h2n⟩, h2⟩, h1⟩, h0n⟩, h0⟩ := h
  rw [Nat.blt_eq] at hcd hsc
  have e2n : S.pen.a2n = 0 := Nat.eq_of_beq_eq_true h2n
  have e0n : S.pen.a0n = 0 := Nat.eq_of_beq_eq_true h0n
  have e2 : (S.pen.a2p : ℝ) * cd = cn * (2 ^ sP * S.sc) := by
    have := Nat.eq_of_beq_eq_true h2
    have h' : S.pen.a2p * cd = cn * (2 ^ sP * S.sc) := this
    exact_mod_cast h'
  have e1 : (S.pen.a1p : ℝ) * cd * 2 ^ tb + 2 * cn * tp * (2 ^ sP * S.sc)
      = (S.pen.a1n : ℝ) * cd * 2 ^ tb + 2 * cn * tn * (2 ^ sP * S.sc) := by
    have := Nat.eq_of_beq_eq_true h1
    have h' : S.pen.a1p * cd * 2 ^ tb + 2 * cn * tp * (2 ^ sP * S.sc)
        = S.pen.a1n * cd * 2 ^ tb + 2 * cn * tn * (2 ^ sP * S.sc) := this
    exact_mod_cast h'
  have e0 : (S.pen.a0p : ℝ) * cd * (2 ^ tb) ^ 2 = cn * ((tp : ℝ) * tp + tn * tn) * (2 ^ sP * S.sc) := by
    have := Nat.eq_of_beq_eq_true h0
    have h' : S.pen.a0p * cd * 4 ^ tb = cn * (tp * tp + tn * tn) * (2 ^ sP * S.sc) := this
    have h4 : (4 : ℝ) ^ tb = (2 ^ tb) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [← h4]
    exact_mod_cast h'
  have htt : (tp : ℝ) * tn = 0 := by
    rcases ht0 with e | e
    · rw [Nat.eq_of_beq_eq_true e]
      simp
    · rw [Nat.eq_of_beq_eq_true e]
      simp
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hD : (0 : ℝ) < 2 ^ sP * (S.sc : ℝ) := by
    have : (0 : ℝ) < S.sc := by exact_mod_cast hsc
    positivity
  have hE : (0 : ℝ) < 2 ^ tb := by positivity
  unfold Pen.val
  rw [e2n, e0n]
  simp only [Nat.cast_zero, sub_zero]
  have key : ((S.pen.a0p : ℝ) + ((S.pen.a1p : ℝ) - S.pen.a1n) * t + (S.pen.a2p : ℝ) * t ^ 2) * (cd * (2 ^ tb) ^ 2)
      = cn * (2 ^ sP * S.sc) * (2 ^ tb * t - ((tp : ℝ) - tn)) ^ 2 := by
    linear_combination e0 + (2 ^ tb * t) * e1 + ((2 ^ tb) ^ 2 * t ^ 2) * e2 + (2 * cn * (2 ^ sP * S.sc)) * htt
  have h1' : (S.pen.a0p : ℝ) + ((S.pen.a1p : ℝ) - S.pen.a1n) * t + (S.pen.a2p : ℝ) * t ^ 2
      = cn * (2 ^ sP * S.sc) * (2 ^ tb * t - ((tp : ℝ) - tn)) ^ 2 / (cd * (2 ^ tb) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    exact key
  rw [h1']
  field_simp

section Conf

variable {N : ℕ} {x : Fin N → EuclideanSpace ℝ (Fin 3)} {p : ℕ → Fin N}

/-- **The penalized energy on the cell of a certificate.** With the polynomials `pen = (cn / cd) (t - τ)²`, the
energy minus `(cn / cd) ∑ (t_ij - τ_ij)²` exceeds `tp / tq`; the centre `τ_ij` is that of the numbers of the two
points. -/
theorem conf_of_rows {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq cn cd tb T : ℕ}
    {l : List (List Sign2)} (H : CertHolds2 P Q C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant2 P C Dm sP (signOfRows l)) (hb : boundOk2 P C xs sP M tp tq = true)
    (hones : onesOk N P.q C Dm = true) (hpens : pensAre N cn cd tb T sP l = true) (hx : Sep x) (hp : InjOn' p N)
    (hin : InCell N Dm.iv x p) :
    (tp : ℝ) / tq < energy x - (cn : ℝ) / cd * ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
      (inner ℝ (x i) (x j)
        - tauV T tb (min (clsOf p N i) (clsOf p N j)) (max (clsOf p N i) (clsOf p N j))) ^ 2 := by
  have hS := inSource2_of_cell hones hx hp hin
  have h := energy2_gt_fin H hdom hmin hb hS
  obtain ⟨hq, h1, h0, hcuts⟩ := onesOk_sound hones
  have hN0 : C.n N = 0 := h0 N le_rfl hq
  have hlt := clsOf_lt_all hS.lab hq hN0
  have e : ∀ i j : Fin N, i < j →
      potV sP (signOfRows l) (clsOf p N i) (clsOf p N j) (inner ℝ (x i) (x j))
        = 1 / ‖x i - x j‖ - (cn : ℝ) / cd * (inner ℝ (x i) (x j)
          - tauV T tb (min (clsOf p N i) (clsOf p N j)) (max (clsOf p N i) (clsOf p N j))) ^ 2 := by
    intro i j hij
    have ei := clsOf_lt (hlt i)
    have ej := clsOf_lt (hlt j)
    have hne : clsOf p N i ≠ clsOf p N j := fun e => (ne_of_lt hij) (by rw [← ei, ← ej, e])
    have hmm : min (clsOf p N i) (clsOf p N j) < max (clsOf p N i) (clsOf p N j) := by
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · rw [min_eq_left h'.le, max_eq_right h'.le]
        exact h'
      · rw [min_eq_right h'.le, max_eq_left h'.le]
        exact h'
    have hmax : max (clsOf p N i) (clsOf p N j) < N := max_lt (hlt i) (hlt j)
    have hpen := (allN_iff _ _).mp ((allN_iff _ _).mp hpens _ hmax) _ hmm
    unfold potV
    rw [penIs_val hpen, one_div_dist (hx.unit i) (hx.unit j)]
    rfl
  have hsum : ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        potV sP (signOfRows l) (clsOf p N i) (clsOf p N j) (inner ℝ (x i) (x j))
      = energy x - (cn : ℝ) / cd * ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        (inner ℝ (x i) (x j)
          - tauV T tb (min (clsOf p N i) (clsOf p N j)) (max (clsOf p N i) (clsOf p N j))) ^ 2 := by
    unfold energy
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    exact e i j (mem_filter.mp hj).2
  rw [hsum] at h
  exact h

end Conf

end N11.Circ
