module

public import CAP.Wsos.BoundValue

/-!
# The domain of a typed certificate in the terms of the source

The source declares the domain of a typed certificate by an interval for the inner products of every
pair type and by further polynomial inequalities for a triple type (`Dom`). `InSource` states that
labelled distinct points of the unit sphere of `ℝ⁴` lie in this domain.

`inDomain_of_source`: if the check `domOk` succeeds, then such points lie in the domain of the checker
(`InDomain`), which is the hypothesis of the theorem of the schema. The proof shows that every
generator that the check allows is nonnegative at the three inner products of a triple of points:

* the generators of the end points of the intervals, by the intervals;
* the Gram determinant of three unit vectors (`gram3_nonneg`, from a frame in `ℝ⁴`);
* `2 + 2 u - (v + t) ^ 2`, `2 - 2 u - (v - t) ^ 2` and their permutations, by the inequality of Cauchy and
  Schwarz for the sum or the difference of two points and the third one (`cauchy_pair`, `cauchy_pair_sub`);
* the cuts of the list, which are hypotheses of `InSource`.

A generator is homogeneous in the checker: `genV_hom` relates it to its value `gval` at the inner
products.
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

/-! ## Values -/

/-- The left end point of an interval. -/
noncomputable def Ival.lo (I : Ival) : ℝ := ((I.lp : ℝ) - (I.ln : ℝ)) / (I.ld : ℝ)

/-- The right end point of an interval. -/
noncomputable def Ival.hi (I : Ival) : ℝ := ((I.hp : ℝ) - (I.hn : ℝ)) / (I.hd : ℝ)

/-- The value of a generator at three inner products `u`, `v`, `t`. -/
noncomputable def gval (g : Gen) (u v t : ℝ) : ℝ :=
  (g.terms.map fun τ => ((τ.cp : ℝ) - (τ.cn : ℝ)) * (u ^ τ.e1 * v ^ τ.e2 * t ^ τ.e3)).sum

theorem termV_hom (E u v t : ℝ) (deg : ℕ) (τ : Term) (h : τ.e1 + τ.e2 + τ.e3 ≤ deg) :
    termV E (E * u) (E * v) (E * t) deg τ
      = E ^ deg * (((τ.cp : ℝ) - (τ.cn : ℝ)) * (u ^ τ.e1 * v ^ τ.e2 * t ^ τ.e3)) := by
  have e : E ^ deg = E ^ (deg - (τ.e1 + τ.e2 + τ.e3)) * (E ^ τ.e1 * E ^ τ.e2 * E ^ τ.e3) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold termV
  rw [e, mul_pow, mul_pow, mul_pow]
  ring

theorem terms_hom (E u v t : ℝ) (deg : ℕ) : ∀ terms : List Term, termsOk deg terms = true →
    (terms.map (termV E (E * u) (E * v) (E * t) deg)).sum
      = E ^ deg * (terms.map fun τ => ((τ.cp : ℝ) - (τ.cn : ℝ)) * (u ^ τ.e1 * v ^ τ.e2 * t ^ τ.e3)).sum
  | [], _ => by simp
  | τ :: l, h => by
    rw [termsOk_cons, Bool.and_eq_true, Nat.ble_eq] at h
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, terms_hom E u v t deg l h.2,
      termV_hom E u v t deg τ h.1]
    ring

/-- A generator of the checker at `E` times three inner products is `E ^ deg` times its value. -/
theorem genV_hom (E u v t : ℝ) (g : Gen) (h : termsOk g.deg g.terms = true) :
    genV E (E * u) (E * v) (E * t) g = E ^ g.deg * gval g u v t :=
  terms_hom E u v t g.deg g.terms h

theorem gval_lo (I : Ival) (e1 e2 e3 : ℕ) (u v t : ℝ) :
    gval (loGen I e1 e2 e3) u v t = (I.ld : ℝ) * (u ^ e1 * v ^ e2 * t ^ e3) - ((I.lp : ℝ) - (I.ln : ℝ)) := by
  simp only [gval, loGen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, Nat.cast_zero]
  ring

theorem gval_hi (I : Ival) (e1 e2 e3 : ℕ) (u v t : ℝ) :
    gval (hiGen I e1 e2 e3) u v t = ((I.hp : ℝ) - (I.hn : ℝ)) - (I.hd : ℝ) * (u ^ e1 * v ^ e2 * t ^ e3) := by
  simp only [gval, hiGen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, Nat.cast_zero]
  ring

theorem gval_det (u v t : ℝ) : gval detGen u v t = 1 - u ^ 2 - v ^ 2 - t ^ 2 + 2 * u * v * t := by
  simp only [gval, detGen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csU (u v t : ℝ) : gval csGenU u v t = 2 + 2 * u - (v + t) ^ 2 := by
  simp only [gval, csGenU, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csV (u v t : ℝ) : gval csGenV u v t = 2 + 2 * v - (u + t) ^ 2 := by
  simp only [gval, csGenV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csT (u v t : ℝ) : gval csGenT u v t = 2 + 2 * t - (u + v) ^ 2 := by
  simp only [gval, csGenT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csUm (u v t : ℝ) : gval csGenUm u v t = 2 - 2 * u - (v - t) ^ 2 := by
  simp only [gval, csGenUm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csVm (u v t : ℝ) : gval csGenVm u v t = 2 - 2 * v - (u - t) ^ 2 := by
  simp only [gval, csGenVm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gval_csTm (u v t : ℝ) : gval csGenTm u v t = 2 - 2 * t - (u - v) ^ 2 := by
  simp only [gval, csGenTm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  ring

/-! ## Three unit vectors -/

/-- The Gram determinant of three unit vectors of `ℝ⁴` is nonnegative. -/
theorem gram3_nonneg (a b c : EuclideanSpace ℝ (Fin 4)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    0 ≤ 1 - inner ℝ a b ^ 2 - inner ℝ a c ^ 2 - inner ℝ b c ^ 2 + 2 * inner ℝ a b * inner ℝ a c * inner ℝ b c := by
  obtain ⟨p, q, r, h⟩ := frame_coords4 a ha
  have hbb := h b b
  have hcc := h c c
  have hbc := h b c
  rw [real_inner_self_eq_norm_sq, hb, one_pow] at hbb
  rw [real_inner_self_eq_norm_sq, hc, one_pow] at hcc
  have h1 : 1 - inner ℝ a b ^ 2 = p b ^ 2 + q b ^ 2 + r b ^ 2 := by linear_combination hbb
  have h2 : 1 - inner ℝ a c ^ 2 = p c ^ 2 + q c ^ 2 + r c ^ 2 := by linear_combination hcc
  have h3 : inner ℝ b c - inner ℝ a b * inner ℝ a c = p b * p c + q b * q c + r b * r c := by
    linear_combination hbc
  have e : 1 - inner ℝ a b ^ 2 - inner ℝ a c ^ 2 - inner ℝ b c ^ 2 + 2 * inner ℝ a b * inner ℝ a c * inner ℝ b c
      = (1 - inner ℝ a b ^ 2) * (1 - inner ℝ a c ^ 2) - (inner ℝ b c - inner ℝ a b * inner ℝ a c) ^ 2 := by ring
  have e2 : (p b ^ 2 + q b ^ 2 + r b ^ 2) * (p c ^ 2 + q c ^ 2 + r c ^ 2) - (p b * p c + q b * q c + r b * r c) ^ 2
      = (p b * q c - q b * p c) ^ 2 + (p b * r c - r b * p c) ^ 2 + (q b * r c - r b * q c) ^ 2 := by ring
  rw [e, h1, h2, h3, e2]
  positivity

/-- The inequality of Cauchy and Schwarz for the sum of two unit vectors and a third one. -/
theorem cauchy_pair (a b c : EuclideanSpace ℝ (Fin 4)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    0 ≤ 2 + 2 * inner ℝ a b - (inner ℝ a c + inner ℝ b c) ^ 2 := by
  have h1 : inner ℝ (a + b) c = inner ℝ a c + inner ℝ b c := inner_add_left a b c
  have h2 : ‖a + b‖ ^ 2 = 2 + 2 * inner ℝ a b := by
    rw [norm_add_sq_real, ha, hb]
    ring
  have h3 : |inner ℝ (a + b) c| ≤ ‖a + b‖ * ‖c‖ := abs_real_inner_le_norm (a + b) c
  rw [hc, mul_one] at h3
  have h4 : inner ℝ (a + b) c ^ 2 ≤ ‖a + b‖ ^ 2 := sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2
  rw [h1, h2] at h4
  linarith

/-- The same for the difference of two unit vectors. -/
theorem cauchy_pair_sub (a b c : EuclideanSpace ℝ (Fin 4)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    0 ≤ 2 - 2 * inner ℝ a b - (inner ℝ a c - inner ℝ b c) ^ 2 := by
  have h1 : inner ℝ (a - b) c = inner ℝ a c - inner ℝ b c := inner_sub_left a b c
  have h2 : ‖a - b‖ ^ 2 = 2 - 2 * inner ℝ a b := by
    rw [norm_sub_sq_real, ha, hb]
    ring
  have h3 : |inner ℝ (a - b) c| ≤ ‖a - b‖ * ‖c‖ := abs_real_inner_le_norm (a - b) c
  rw [hc, mul_one] at h3
  have h4 : inner ℝ (a - b) c ^ 2 ≤ ‖a - b‖ ^ 2 := sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2
  rw [h1, h2] at h4
  linarith

/-! ## The intervals -/

theorem lo_nonneg {I : Ival} (hld : 0 < I.ld) {z : ℝ} (h : I.lo ≤ z) : 0 ≤ (I.ld : ℝ) * z - ((I.lp : ℝ) - (I.ln : ℝ)) := by
  have hR : (0 : ℝ) < I.ld := Nat.cast_pos.mpr hld
  have h' : (I.lp : ℝ) - (I.ln : ℝ) ≤ z * I.ld := (div_le_iff₀ hR).mp h
  linarith

theorem hi_nonneg {I : Ival} (hhd : 0 < I.hd) {z : ℝ} (h : z ≤ I.hi) : 0 ≤ ((I.hp : ℝ) - (I.hn : ℝ)) - (I.hd : ℝ) * z := by
  have hR : (0 : ℝ) < I.hd := Nat.cast_pos.mpr hhd
  have h' : z * I.hd ≤ (I.hp : ℝ) - (I.hn : ℝ) := (le_div_iff₀ hR).mp h
  linarith

theorem boxIn_pos {P : Params} {b : Box} {I : Ival} (h : boxIn P b I = true) : 0 < I.ld ∧ 0 < I.hd := by
  unfold boxIn at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-- The box of the checker contains the interval. -/
theorem boxIn_sound {P : Params} {b : Box} {I : Ival} (h : boxIn P b I = true) {t : ℝ} (h1 : I.lo ≤ t)
    (h2 : t ≤ I.hi) : InBox b ((2 : ℝ) ^ P.m * t) := by
  unfold boxIn at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨hld, hhd⟩, hlo⟩, hhi⟩ := h
  have hldR : (0 : ℝ) < I.ld := Nat.cast_pos.mpr hld
  have hhdR : (0 : ℝ) < I.hd := Nat.cast_pos.mpr hhd
  have h1' : (I.lp : ℝ) - (I.ln : ℝ) ≤ t * I.ld := (div_le_iff₀ hldR).mp h1
  have h2' : t * I.hd ≤ (I.hp : ℝ) - (I.hn : ℝ) := (le_div_iff₀ hhdR).mp h2
  rw [shl_eq, shl_eq] at hlo hhi
  have hlo' : b.cp * I.ld + I.ln * 2 ^ P.m ≤ I.lp * 2 ^ P.m + (b.cn + b.rho) * I.ld := hlo
  have hhi' : I.hp * 2 ^ P.m + b.cn * I.hd ≤ I.hn * 2 ^ P.m + (b.cp + b.rho) * I.hd := hhi
  have hloR : (b.cp : ℝ) * I.ld + I.ln * 2 ^ P.m ≤ I.lp * 2 ^ P.m + ((b.cn : ℝ) + b.rho) * I.ld := by
    exact_mod_cast hlo'
  have hhiR : (I.hp : ℝ) * 2 ^ P.m + b.cn * I.hd ≤ I.hn * 2 ^ P.m + ((b.cp : ℝ) + b.rho) * I.hd := by
    exact_mod_cast hhi'
  have hE : (0 : ℝ) < 2 ^ P.m := by positivity
  have m1 := mul_le_mul_of_nonneg_left h1' hE.le
  have m2 := mul_le_mul_of_nonneg_left h2' hE.le
  have g1 : ((b.cp : ℝ) - b.cn - b.rho) * I.ld ≤ (2 ^ P.m * t) * I.ld := by linarith
  have g2 : (2 ^ P.m * t) * I.hd ≤ ((b.cp : ℝ) - b.cn + b.rho) * I.hd := by linarith
  have k1 := le_of_mul_le_mul_right g1 hldR
  have k2 := le_of_mul_le_mul_right g2 hhdR
  unfold InBox
  rw [abs_le]
  constructor <;> linarith

/-! ## The lists of the check -/

theorem termBeq_eq {s t : Term} (h : termBeq s t = true) : s = t := by
  unfold termBeq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases s
  cases t
  simp only [Term.mk.injEq]
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5⟩

theorem termsBeq_eq : ∀ {l l' : List Term}, termsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | s :: l, t :: l', h => by
    have h' : (termBeq s t && termsBeq l l') = true := h
    rw [Bool.and_eq_true] at h'
    rw [termBeq_eq h'.1, termsBeq_eq h'.2]

theorem genBeq_eq {g k : Gen} (h : genBeq g k = true) : g = k := by
  unfold genBeq at h
  rw [Bool.and_eq_true] at h
  cases g
  cases k
  simp only [Gen.mk.injEq]
  exact ⟨Nat.eq_of_beq_eq_true h.1, termsBeq_eq h.2⟩

theorem genMem_mem {g : Gen} : ∀ {l : List Gen}, genMem g l = true → g ∈ l
  | [], h => by cases h
  | k :: l, h => by
    have h' : (genBeq g k || genMem g l) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · rw [genBeq_eq h']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (genMem_mem h')

theorem gensIn_mem {allowed : List Gen} : ∀ {l : List Gen}, gensIn allowed l = true → ∀ g ∈ l, g ∈ allowed
  | [], _, g, hg => by simp at hg
  | k :: l, h, g, hg => by
    have h' : (genMem k allowed && gensIn allowed l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hg with e | hg
    · rw [e]
      exact genMem_mem h'.1
    · exact gensIn_mem h'.2 g hg

theorem weightsIn_mem {allowed : List Gen} : ∀ {l : List Weight}, weightsIn allowed l = true →
    ∀ w ∈ l, gensIn allowed w.gens = true
  | [], _, w, hw => by simp at hw
  | k :: l, h, w, hw => by
    have h' : (gensIn allowed k.gens && weightsIn allowed l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hw with e | hw
    · rw [e]
      exact h'.1
    · exact weightsIn_mem h'.2 w hw

theorem allX_iff (f : TyX → Bool) : ∀ l : List TyX, allX f l = true ↔ ∀ X ∈ l, f X = true
  | [] => ⟨fun _ X hX => by simp at hX, fun _ => rfl⟩
  | X :: l => by
    show (f X && allX f l) = true ↔ _
    rw [Bool.and_eq_true, allX_iff f l, List.forall_mem_cons]

theorem findCuts_cons (a b c : ℕ) (X : Cuts) (l : List Cuts) :
    findCuts a b c (X :: l) = cond (Nat.beq X.a a && Nat.beq X.b b && Nat.beq X.c c) X.gens (findCuts a b c l) := rfl

theorem findCuts_mem {a b c : ℕ} {g : Gen} : ∀ {l : List Cuts}, g ∈ findCuts a b c l → ∃ X ∈ l, g ∈ X.gens
  | [], h => by
    have h' : g ∈ ([] : List Gen) := h
    simp at h'
  | X :: l, h => by
    rw [findCuts_cons] at h
    cases hk : (Nat.beq X.a a && Nat.beq X.b b && Nat.beq X.c c) with
    | true =>
      rw [hk] at h
      exact ⟨X, List.mem_cons_self, h⟩
    | false =>
      rw [hk] at h
      obtain ⟨Y, hY, hg⟩ := findCuts_mem (l := l) h
      exact ⟨Y, List.mem_cons_of_mem _ hY, hg⟩

theorem cutsOk_mem : ∀ {l : List Cuts}, cutsOk l = true → ∀ X ∈ l, gensOk X.gens = true
  | [], _, X, hX => by simp at hX
  | Y :: l, h, X, hX => by
    have h' : (gensOk Y.gens && cutsOk l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hX with e | hX
    · rw [e]
      exact h'.1
    · exact cutsOk_mem h'.2 X hX

theorem gensOk_mem : ∀ {l : List Gen}, gensOk l = true → ∀ g ∈ l, termsOk g.deg g.terms = true
  | [], _, g, hg => by simp at hg
  | k :: l, h, g, hg => by
    rw [gensOk_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hg with e | hg
    · rw [e]
      exact h.1
    · exact gensOk_mem h.2 g hg

/-! ## The generators of the domain at three unit vectors -/

/-- The inner product `z` lies in the interval `I`, whose denominators are positive. -/
def IvHolds (I : Ival) (z : ℝ) : Prop := 0 < I.ld ∧ 0 < I.hd ∧ I.lo ≤ z ∧ z ≤ I.hi

theorem mono100 (u v t : ℝ) : u ^ 1 * v ^ 0 * t ^ 0 = u := by ring

theorem mono010 (u v t : ℝ) : u ^ 0 * v ^ 1 * t ^ 0 = v := by ring

theorem mono001 (u v t : ℝ) : u ^ 0 * v ^ 0 * t ^ 1 = t := by ring

/-- Every generator that the check of the domain allows is nonnegative at three unit vectors whose inner
products lie in the intervals and satisfy the cuts. -/
theorem domGens_nonneg (m : ℕ) (Dm : Dom) (ca cb cc : ℕ) (a b c : EuclideanSpace ℝ (Fin 4))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (h1 : IvHolds (Dm.iv ca cb) (inner ℝ a b)) (h2 : IvHolds (Dm.iv ca cc) (inner ℝ a c))
    (h3 : IvHolds (Dm.iv cb cc) (inner ℝ b c))
    (hcut : ∀ g ∈ findCuts ca cb cc Dm.cuts,
      termsOk g.deg g.terms = true ∧ 0 ≤ gval g (inner ℝ a b) (inner ℝ a c) (inner ℝ b c))
    {g : Gen} (hg : g ∈ domGens Dm ca cb cc) :
    0 ≤ genV ((2 : ℝ) ^ m) ((2 : ℝ) ^ m * inner ℝ a b) ((2 : ℝ) ^ m * inner ℝ a c) ((2 : ℝ) ^ m * inner ℝ b c) g := by
  have key : ∀ k : Gen, termsOk k.deg k.terms = true → 0 ≤ gval k (inner ℝ a b) (inner ℝ a c) (inner ℝ b c) →
      0 ≤ genV ((2 : ℝ) ^ m) ((2 : ℝ) ^ m * inner ℝ a b) ((2 : ℝ) ^ m * inner ℝ a c) ((2 : ℝ) ^ m * inner ℝ b c) k := by
    intro k hok hv
    rw [genV_hom _ _ _ _ k hok]
    exact mul_nonneg (by positivity) hv
  unfold domGens at hg
  simp only [List.mem_cons] at hg
  rcases hg with e | e | e | e | e | e | e | e | e | e | e | e | e | hg
  · rw [e]
    refine key _ rfl ?_
    rw [gval_lo, mono100]
    exact lo_nonneg h1.1 h1.2.2.1
  · rw [e]
    refine key _ rfl ?_
    rw [gval_hi, mono100]
    exact hi_nonneg h1.2.1 h1.2.2.2
  · rw [e]
    refine key _ rfl ?_
    rw [gval_lo, mono010]
    exact lo_nonneg h2.1 h2.2.2.1
  · rw [e]
    refine key _ rfl ?_
    rw [gval_hi, mono010]
    exact hi_nonneg h2.2.1 h2.2.2.2
  · rw [e]
    refine key _ rfl ?_
    rw [gval_lo, mono001]
    exact lo_nonneg h3.1 h3.2.2.1
  · rw [e]
    refine key _ rfl ?_
    rw [gval_hi, mono001]
    exact hi_nonneg h3.2.1 h3.2.2.2
  · rw [e]
    refine key _ rfl ?_
    rw [gval_det]
    exact gram3_nonneg a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csU]
    exact cauchy_pair a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csV]
    have h := cauchy_pair a c b ha hc hb
    rw [real_inner_comm b c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csT]
    have h := cauchy_pair b c a hb hc ha
    rw [real_inner_comm a b, real_inner_comm a c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csUm]
    exact cauchy_pair_sub a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csVm]
    have h := cauchy_pair_sub a c b ha hc hb
    rw [real_inner_comm b c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csTm]
    have h := cauchy_pair_sub b c a hb hc ha
    rw [real_inner_comm a b, real_inner_comm a c] at h
    exact h
  · exact key g (hcut g hg).1 (hcut g hg).2

/-! ## Points in the domain of the source -/

section Points

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The number of pairs of points with the classes of two distinct points is positive. -/
theorem Labelling.pcnt_pos {q : ℕ} {C : Cert} {cls : ι → ℕ} (L : Labelling q C cls) {i j : ι} (hij : i ≠ j) :
    0 < pcnt C (cls i) (cls j) := by
  have hi : 0 < C.n (cls i) := by
    rw [← L.card _ (L.lt i)]
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, rfl⟩⟩
  have hj : 0 < C.n (cls j) - (if cls j = cls i then 1 else 0) := by
    rw [← L.card _ (L.lt j)]
    split_ifs with h
    · have h2 : 1 < (univ.filter fun k => cls k = cls j).card :=
        one_lt_card.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, h.symm⟩, j, mem_filter.mpr ⟨mem_univ j, rfl⟩, hij⟩
      omega
    · have h2 : 0 < (univ.filter fun k => cls k = cls j).card :=
        card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_univ j, rfl⟩⟩
      omega
  rw [pcnt_eq]
  exact Nat.mul_pos hi hj

/-- Distinct points of the unit sphere of `ℝ⁴` with classes, in the domain of a typed certificate as the
source declares it: the inner product of every pair lies in the interval of its pair type, and the three
inner products of every triple satisfy the further inequalities of its triple type. -/
structure InSource (q : ℕ) (C : Cert) (Dm : Dom) (cls : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 4)) : Prop where
  lab : Labelling q C cls
  unit : ∀ i, ‖x i‖ = 1
  /-- the points are distinct -/
  inj : Function.Injective x
  iv : ∀ i j, i ≠ j → cls i ≤ cls j →
    (Dm.iv (cls i) (cls j)).lo ≤ inner ℝ (x i) (x j) ∧ inner ℝ (x i) (x j) ≤ (Dm.iv (cls i) (cls j)).hi
  cuts : ∀ i j k, Distinct3 i j k → cls i ≤ cls j → cls j ≤ cls k →
    ∀ g ∈ findCuts (cls i) (cls j) (cls k) Dm.cuts,
      0 ≤ gval g (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))

variable {P : Params} {C : Cert} {xs : List TyX} {Dm : Dom} {cls : ι → ℕ} {x : ι → EuclideanSpace ℝ (Fin 4)}

omit [DecidableEq ι] in
/-- The box of a pair of points contains the interval of its pair type. -/
theorem pair_boxIn (hdom : domOk P C Dm xs = true) (L : Labelling P.q C cls) {i j : ι} (hij : i ≠ j)
    (hle : cls i ≤ cls j) : boxIn P (C.box (cls i) (cls j)) (Dm.iv (cls i) (cls j)) = true := by
  unfold domOk at hdom
  rw [Bool.and_eq_true, Bool.and_eq_true] at hdom
  have h : (Nat.blt (cls j) (cls i) || Nat.beq (pcnt C (cls i) (cls j)) 0
      || boxIn P (C.box (cls i) (cls j)) (Dm.iv (cls i) (cls j))) = true :=
    (all2N_iff _ _).mp hdom.1.1 (cls i) (L.lt i) (cls j) (L.lt j)
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [Nat.blt_eq] at h
    omega
  · exact absurd (Nat.eq_of_beq_eq_true h) (L.pcnt_pos hij).ne'
  · exact h

/-- **The domain of the checker contains the domain of the source.** -/
theorem inDomain_of_source (H : CertHolds P C xs) (hdom : domOk P C Dm xs = true) (hS : InSource P.q C Dm cls x) :
    InDomain P C xs cls x := by
  have L := hS.lab
  have hbox : ∀ i j : ι, i ≠ j → cls i ≤ cls j → IvHolds (Dm.iv (cls i) (cls j)) (inner ℝ (x i) (x j)) :=
    fun i j hij hle => ⟨(boxIn_pos (pair_boxIn hdom L hij hle)).1, (boxIn_pos (pair_boxIn hdom L hij hle)).2,
      (hS.iv i j hij hle).1, (hS.iv i j hij hle).2⟩
  refine ⟨L, hS.unit, ?_, ?_⟩
  · intro i j hij hle
    exact boxIn_sound (pair_boxIn hdom L hij hle) (hS.iv i j hij hle).1 (hS.iv i j hij hle).2
  · intro i j k hd hij hjk w hw g hg
    have m1 : 0 < mult C (cls i) (cls j) (cls k) := L.mult_pos hd
    have m2 : 0 < mult C (cls i) (cls k) (cls j) := L.mult_pos ⟨hd.2.1, hd.1, hd.2.2.symm⟩
    have m3 : 0 < mult C (cls j) (cls k) (cls i) := L.mult_pos ⟨hd.2.2, hd.1.symm, hd.2.1.symm⟩
    obtain ⟨hmem, ea, eb, ec⟩ :=
      findX_spec _ _ _ xs (H.cover _ (L.lt i) _ (L.lt j) _ (L.lt k) hij hjk m3 m2 m1)
    have hdom' := hdom
    unfold domOk at hdom'
    rw [Bool.and_eq_true, Bool.and_eq_true] at hdom'
    have hw' : weightsIn (domGens Dm (findX (cls i) (cls j) (cls k) xs).a (findX (cls i) (cls j) (cls k) xs).b
        (findX (cls i) (cls j) (cls k) xs).c) (findX (cls i) (cls j) (cls k) xs).weights = true :=
      (allX_iff _ xs).mp hdom'.1.2 _ hmem
    rw [ea, eb, ec] at hw'
    have hgm : g ∈ domGens Dm (cls i) (cls j) (cls k) := gensIn_mem (weightsIn_mem hw' w hw) g hg
    have hcut : ∀ g ∈ findCuts (cls i) (cls j) (cls k) Dm.cuts, termsOk g.deg g.terms = true
        ∧ 0 ≤ gval g (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k)) := by
      intro g' hg'
      obtain ⟨Y, hY, hgY⟩ := findCuts_mem hg'
      exact ⟨gensOk_mem (cutsOk_mem hdom'.2 Y hY) g' hgY, hS.cuts i j k hd hij hjk g' hg'⟩
    exact domGens_nonneg P.m Dm (cls i) (cls j) (cls k) (x i) (x j) (x k) (hS.unit i) (hS.unit j) (hS.unit k)
      (hbox i j hd.1 hij) (hbox i k hd.2.1 (le_trans hij hjk)) (hbox j k hd.2.2 hjk) hcut hgm

end Points

end CAP.Wsos
