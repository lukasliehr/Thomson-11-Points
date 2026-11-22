module

public import N11.ParallelResearch1.Circ.Tables

/-!
# Soundness of the checks over lists and of the bound with a table of the constants

* `tysOk_holds`: all triple types of an accepted list satisfy `TyHolds2`; `tyAll2_append` joins lists.
* `gramsOk_sound`: the hypothesis `gram` of `CertHolds2` from the one check of all Gram matrices.
* `boundOk3_imp`: if `boundOk3` accepts, the tables hold the constants of the list, and the list contains every
  triple type that occurs, then `boundOk2` accepts: the two checks compare the same numbers.
* `pensZeroR_val`: without polynomials `pen` the potential of every pair type is the Coulomb potential.
* `coulomb2_gt_rows`: the theorem of a certificate without polynomials `pen`, for tables in rows.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-! ## Lists of triple types -/

theorem tysOk_holds {P : Params} {Q : ℕ} {C : Cert} (hL : LayoutInj P.D P.k1 P.k2) :
    ∀ (l : List TyX), tysOk P Q C l = true → ∀ X ∈ l, TyHolds2 P (tyOf2 Q C X)
  | [], _, X, hX => by simp at hX
  | Y :: l, h, X, hX => by
    have h' : (checkTy2 P (tyOf2 Q C Y) && tysOk P Q C l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hX with rfl | hX
    · exact checkTy2_holds hL h'.1
    · exact tysOk_holds hL l h'.2 X hX

theorem tyAll2_append {P : Params} {Q : ℕ} {C : Cert} {l1 l2 : List TyX} (h1 : ∀ X ∈ l1, TyHolds2 P (tyOf2 Q C X))
    (h2 : ∀ X ∈ l2, TyHolds2 P (tyOf2 Q C X)) : ∀ X ∈ l1 ++ l2, TyHolds2 P (tyOf2 Q C X) := by
  intro X hX
  rcases List.mem_append.mp hX with h | h
  · exact h1 X h
  · exact h2 X h

/-! ## The Gram matrices -/

theorem gramRowOk_all {P : Params} : ∀ (ys : List (List ℕ)) (n : ℕ) (gs : List ℕ), gramRowOk P ys n gs = true →
    GramAll P n ys gs
  | [], _, [], _ => trivial
  | [], _, _ :: _, h => by
    have h' : false = true := h
    cases h'
  | _ :: _, _, [], h => by
    have h' : false = true := h
    cases h'
  | y :: ys, n, g :: gs, h => by
    have h' : (gramOk P n y g && gramRowOk P ys (Nat.pred n) gs) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨gramOk_holds h'.1, gramRowOk_all ys (n - 1) gs h'.2⟩

/-- The Gram matrices of the rooted blocks have the form `Y Yᵀ`. -/
theorem gramsOk_sound {P : Params} {C : Cert} {ys : List (List (List ℕ))} {Q : ℕ} (h : gramsOk P C ys Q = true) :
    ∀ a < Q, ∃ cols : ℕ → List ℕ,
      ∀ k < (C.gram a).length, GramHolds P (P.d - k) (cols k) ((C.gram a).getD k 0) := by
  intro a ha
  exact gram_of_all (gramRowOk_all _ _ _ ((allN_iff _ _).mp h a ha))

/-! ## The bound with a table of the constants -/

theorem tmult_key (C : Cert) (X : TyX) : tmult C X = tmultK C X.a X.b X.c := rfl

/-- Three distinct points with the classes `a`, `b`, `c` exist: the three multiplicities are positive. -/
def Occ (C : Cert) (a b c : ℕ) : Prop := 0 < mult C b c a ∧ 0 < mult C a c b ∧ 0 < mult C a b c

theorem Occ.swap12 {C : Cert} {a b c : ℕ} (h : Occ C a b c) : Occ C b a c :=
  ⟨h.2.1, h.1, by rw [mult_comm]; exact h.2.2⟩

theorem Occ.swap23 {C : Cert} {a b c : ℕ} (h : Occ C a b c) : Occ C a c b :=
  ⟨by rw [mult_comm]; exact h.1, h.2.2, h.2.1⟩

theorem occ_of_cnt {C : Cert} {a b c : ℕ} (h : 0 < cnt C a b c) : Occ C a b c := by
  have e : cnt C a b c = C.n a * (C.n b - (if b = a then 1 else 0)) * mult C a b c := by
    show pcnt C a b * mult C a b c = _
    rw [pcnt_eq]
  rw [e] at h
  have h3 : 0 < mult C a b c := Nat.pos_of_mul_pos_left h
  have h12 : 0 < C.n a * (C.n b - (if b = a then 1 else 0)) := Nat.pos_of_mul_pos_right h
  have h1 : 0 < C.n a := Nat.pos_of_mul_pos_right h12
  have h2 : 0 < C.n b - (if b = a then 1 else 0) := Nat.pos_of_mul_pos_left h12
  refine ⟨?_, ?_, h3⟩
  · rw [mult_eq] at h3 ⊢
    by_cases hab : a = b
    · subst hab
      by_cases hac : a = c
      · subst hac
        simp only [if_true] at h2 h3 ⊢
        omega
      · have hca : c ≠ a := fun e => hac e.symm
        simp only [if_true, if_neg hac, if_neg hca] at h2 h3 ⊢
        omega
    · have hba : b ≠ a := fun e => hab e.symm
      by_cases hac : a = c
      · subst hac
        simp only [if_true, if_neg hab, if_neg hba] at h2 h3 ⊢
        omega
      · simp only [if_neg hab, if_neg hac] at ⊢
        omega
  · rw [mult_eq] at h3 ⊢
    by_cases hab : a = b
    · subst hab
      by_cases hac : a = c
      · subst hac
        simp only [if_true] at h2 h3 ⊢
        omega
      · have hca : c ≠ a := fun e => hac e.symm
        simp only [if_true, if_neg hac, if_neg hca] at h2 h3 ⊢
        omega
    · have hba : b ≠ a := fun e => hab e.symm
      by_cases hbc : b = c
      · subst hbc
        simp only [if_true, if_neg hab, if_neg hba] at h2 h3 ⊢
        omega
      · simp only [if_neg hba, if_neg hbc] at h2 ⊢
        omega

/-- The sorted triple of three classes that occur occurs. -/
theorem occ_sorted (C : Cert) : ∀ a b c : ℕ, Occ C a b c → Occ C (lo3 a b c) (mid3 a b c) (hi3 a b c) := by
  refine of_sorted (fun x : ℕ => x) (fun a b c => Occ C a b c → Occ C (lo3 a b c) (mid3 a b c) (hi3 a b c)) ?_ ?_ ?_
  · intro a b c hq h
    obtain ⟨e1, e2, e3⟩ := sort3_swap12 a b c
    rw [e1, e2, e3]
    exact hq h.swap12
  · intro a b c hq h
    obtain ⟨e1, e2, e3⟩ := sort3_swap23 a b c
    rw [e1, e2, e3]
    exact hq h.swap23
  · intro a b c hab hbc h
    obtain ⟨e1, e2, e3⟩ := sort3_sorted hab hbc
    rw [e1, e2, e3]
    exact h

theorem sort3_le (a b c : ℕ) : lo3 a b c ≤ mid3 a b c ∧ mid3 a b c ≤ hi3 a b c := by
  rw [lo3_eq, mid3_eq, hi3_eq]
  omega

theorem sort3_lt {q a b c : ℕ} (ha : a < q) (hb : b < q) (hc : c < q) :
    lo3 a b c < q ∧ mid3 a b c < q ∧ hi3 a b c < q := by
  rw [lo3_eq, mid3_eq, hi3_eq]
  omega

theorem constsOk_mem {cP cN : ℕ → ℕ → ℕ → ℕ} : ∀ (l : List TyX), constsOk cP cN l = true →
    ∀ X ∈ l, cP X.a X.b X.c = X.c2p ∧ cN X.a X.b X.c = X.c2n
  | [], _, X, hX => by simp at hX
  | Y :: l, h, X, hX => by
    have h' : (Nat.beq (cP Y.a Y.b Y.c) Y.c2p && Nat.beq (cN Y.a Y.b Y.c) Y.c2n && constsOk cP cN l) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hX with rfl | hX
    · exact ⟨Nat.eq_of_beq_eq_true h'.1.1, Nat.eq_of_beq_eq_true h'.1.2⟩
    · exact constsOk_mem l h'.2 X hX

section Bound

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {cP cN : ℕ → ℕ → ℕ → ℕ}

/-- The triple type of a triple of classes that occurs is in the list, with its key. -/
theorem typeOf_spec (H : CertHolds2 P Q C xs) {a b c : ℕ} (ha : a < P.q) (hb : b < P.q) (hc : c < P.q)
    (h : 0 < cnt C a b c) :
    typeOf xs a b c ∈ xs ∧ (typeOf xs a b c).a = lo3 a b c ∧ (typeOf xs a b c).b = mid3 a b c
      ∧ (typeOf xs a b c).c = hi3 a b c := by
  obtain ⟨o1, o2, o3⟩ := occ_sorted C a b c (occ_of_cnt h)
  obtain ⟨l1, l2, l3⟩ := sort3_lt ha hb hc
  obtain ⟨s1, s2⟩ := sort3_le a b c
  exact findX_spec _ _ _ xs (H.cover _ l1 _ l2 _ l3 s1 s2 o1 o2 o3)

theorem cTerm3_eq (H : CertHolds2 P Q C xs) (hc2 : constsOk cP cN xs = true) (M : ℕ) {a b c : ℕ} (ha : a < P.q)
    (hb : b < P.q) (hc : c < P.q) :
    cTerm3 C cP M a b c = cTerm C xs M (fun X => X.c2p) a b c
      ∧ cTerm3 C cN M a b c = cTerm C xs M (fun X => X.c2n) a b c := by
  rcases Nat.eq_zero_or_pos (cnt C a b c) with h0 | h0
  · have e1 : ∀ cT, cTerm3 C cT M a b c = 0 := by
      intro cT
      unfold cTerm3
      rw [h0]
      rfl
    have e2 : ∀ sel : TyX → ℕ, cTerm C xs M sel a b c = 0 := by
      intro sel
      show cnt C a b c * sel (typeOf xs a b c) * (M / tmult C (typeOf xs a b c)) = 0
      rw [h0]
      simp
    rw [e1, e1, e2, e2]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hmem, ka, kb, kc⟩ := typeOf_spec H ha hb hc h0
    obtain ⟨c1, c2⟩ := constsOk_mem xs hc2 _ hmem
    have hb0 : Nat.beq (cnt C a b c) 0 = false := by
      cases hb' : Nat.beq (cnt C a b c) 0 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb') h0.ne'
    have e1 : ∀ cT, cTerm3 C cT M a b c
        = cnt C a b c * cT (lo3 a b c) (mid3 a b c) (hi3 a b c) * (M / tmultK C (lo3 a b c) (mid3 a b c) (hi3 a b c)) := by
      intro cT
      unfold cTerm3
      rw [hb0]
      rfl
    have e2 : ∀ sel : TyX → ℕ, cTerm C xs M sel a b c
        = cnt C a b c * sel (typeOf xs a b c) * (M / tmult C (typeOf xs a b c)) := fun _ => rfl
    rw [e1, e1, e2, e2, tmult_key, ka, kb, kc]
    rw [ka, kb, kc] at c1 c2
    rw [c1, c2]
    exact ⟨rfl, rfl⟩

theorem divOk3_eq (H : CertHolds2 P Q C xs) (M : ℕ) {a b c : ℕ} (ha : a < P.q) (hb : b < P.q) (hc : c < P.q)
    (h : divOk3 C M a b c = true) : divOk C xs M a b c = true := by
  unfold divOk3 at h
  unfold divOk
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · rcases Nat.eq_zero_or_pos (cnt C a b c) with h0 | h0
    · left
      rw [h0]
      rfl
    · right
      obtain ⟨_, ka, kb, kc⟩ := typeOf_spec H ha hb hc h0
      rw [tmult_key, ka, kb, kc]
      exact h

theorem sum3N_congr {f g : ℕ → ℕ → ℕ → ℕ} {q : ℕ} (h : ∀ a < q, ∀ b < q, ∀ c < q, f a b c = g a b c) :
    sum3N f q = sum3N g q := by
  rw [sum3N_eq, sum3N_eq]
  refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => sum_congr rfl fun c hc => ?_
  exact h a (mem_range.mp ha) b (mem_range.mp hb) c (mem_range.mp hc)

/-- **The bound with a table of the constants.** -/
theorem boundOk3_imp {sP M tp tq : ℕ} (H : CertHolds2 P Q C xs) (h : boundOk3 P C xs cP cN sP M tp tq = true) :
    boundOk2 P C xs sP M tp tq = true := by
  unfold boundOk3 at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hM, htq⟩, hc2⟩, hdiv⟩, hlt⟩ := h
  have eP : sum3N (cTerm3 C cP M) P.q = sum3N (cTerm C xs M fun X => X.c2p) P.q :=
    sum3N_congr fun a ha b hb c hc => (cTerm3_eq H hc2 M ha hb hc).1
  have eN : sum3N (cTerm3 C cN M) P.q = sum3N (cTerm C xs M fun X => X.c2n) P.q :=
    sum3N_congr fun a ha b hb c hc => (cTerm3_eq H hc2 M ha hb hc).2
  have hdiv' : all3N (divOk C xs M) P.q = true :=
    (all3N_iff _ _).mpr fun a ha b hb c hc => divOk3_eq H M ha hb hc ((all3N_iff _ _).mp hdiv a ha b hb c hc)
  rw [eP, eN] at hlt
  unfold boundOk2
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨hM, htq⟩, hdiv'⟩, hlt⟩

end Bound

/-! ## Tables in rows: the potential -/

theorem pensZeroR_nth : ∀ (l : List (List Sign2)), pensZeroR l = true → ∀ a : ℕ, pensZero (nthSL l a) = true
  | [], _, _ => rfl
  | row :: l, h, a => by
    have h' : (pensZero row && pensZeroR l) = true := h
    rw [Bool.and_eq_true] at h'
    cases a with
    | zero => exact h'.1
    | succ a => exact pensZeroR_nth l h'.2 a

/-- If no witness of the table has a polynomial `pen`, the polynomial `pen` of every pair type vanishes. -/
theorem pensZeroR_val {l : List (List Sign2)} (h : pensZeroR l = true) (a b : ℕ) (Dn t : ℝ) :
    (signOfRows l a b).pen.val Dn t = 0 :=
  penZero_val (pensZero_nth _ (pensZeroR_nth l h a) b) Dn t

/-- **The Coulomb energy of points in the domain of a typed certificate without polynomials `pen` exceeds
`tp / tq`** (for a table of witnesses in rows). -/
theorem coulomb2_gt_rows {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq n : ℕ}
    {l : List (List Sign2)} {cls : Fin n → ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (H : CertHolds2 P Q C xs)
    (hdom : domOk P C Dm xs = true) (hmin : Minorant2 P C Dm sP (signOfRows l)) (hpen : pensZeroR l = true)
    (hb : boundOk2 P C xs sP M tp tq = true) (hS : InSource2 P.q C Dm cls x) :
    (tp : ℝ) / tq < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ := by
  have h := energy2_gt_fin H hdom hmin hb hS
  have e : ∀ i j : Fin n, potV sP (signOfRows l) (cls i) (cls j) (inner ℝ (x i) (x j)) = 1 / ‖x i - x j‖ := by
    intro i j
    unfold potV
    rw [pensZeroR_val hpen, sub_zero, one_div_dist (hS.unit i) (hS.unit j)]
  simp only [e] at h
  exact h

end N11.Circ
