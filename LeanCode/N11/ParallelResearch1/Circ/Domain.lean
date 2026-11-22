module

public import CAP.Wsos.Domain
public import N11.ParallelResearch1.Circ.BoundValue

/-!
# The domain of a typed certificate on the two-sphere

`InSource2`: distinct points of the unit sphere of `ℝ³` with classes such that the inner product of every pair
lies in the interval of its pair type (and such that the further inequalities of a triple type hold, if the
domain declares any; the certificates of route G declare none).

`inDomain2_of_source`: if `CAP.Wsos.domOk` accepts, such points lie in the domain of the checker (`InDomain2`):
the boxes contain the intervals, and every generator of a weight is the generator of an end point of an
interval, the Gram determinant, an inequality of Cauchy and Schwarz, or a declared inequality. The proof is
that of `CAP.Wsos.inDomain_of_source`, for three unit vectors of `ℝ³`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

open CAP.ThreePoint (Distinct3)

/-! ## Three unit vectors of `ℝ³` -/

theorem gram3_nonneg3 (a b c : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    0 ≤ 1 - inner ℝ a b ^ 2 - inner ℝ a c ^ 2 - inner ℝ b c ^ 2 + 2 * inner ℝ a b * inner ℝ a c * inner ℝ b c := by
  have h := CAP.ThreePoint.gram_nonneg a b c ha hb hc
  linarith

/-- The inequality of Cauchy and Schwarz for the sum of two unit vectors and a third one. -/
theorem cauchy_pair3 (a b c : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
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
theorem cauchy_pair_sub3 (a b c : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
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

/-- Every generator that the check of the domain allows is nonnegative at three unit vectors of `ℝ³` whose inner
products lie in the intervals and satisfy the cuts. -/
theorem domGens_nonneg3 (m : ℕ) (Dm : Dom) (ca cb cc : ℕ) (a b c : EuclideanSpace ℝ (Fin 3))
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
    exact gram3_nonneg3 a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csU]
    exact cauchy_pair3 a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csV]
    have h := cauchy_pair3 a c b ha hc hb
    rw [real_inner_comm b c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csT]
    have h := cauchy_pair3 b c a hb hc ha
    rw [real_inner_comm a b, real_inner_comm a c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csUm]
    exact cauchy_pair_sub3 a b c ha hb hc
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csVm]
    have h := cauchy_pair_sub3 a c b ha hc hb
    rw [real_inner_comm b c] at h
    exact h
  · rw [e]
    refine key _ rfl ?_
    rw [gval_csTm]
    have h := cauchy_pair_sub3 b c a hb hc ha
    rw [real_inner_comm a b, real_inner_comm a c] at h
    exact h
  · exact key g (hcut g hg).1 (hcut g hg).2

/-! ## Points in the domain of a certificate -/

section Points

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct points of the unit sphere of `ℝ³` with classes, in the domain of a typed certificate: the inner
product of every pair lies in the interval of its pair type, and the three inner products of every triple
satisfy the further inequalities of its triple type. -/
structure InSource2 (q : ℕ) (C : Cert) (Dm : Dom) (cls : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 3)) : Prop where
  lab : Labelling q C cls
  unit : ∀ i, ‖x i‖ = 1
  /-- the points are distinct -/
  inj : Function.Injective x
  iv : ∀ i j, i ≠ j → cls i ≤ cls j →
    (Dm.iv (cls i) (cls j)).lo ≤ inner ℝ (x i) (x j) ∧ inner ℝ (x i) (x j) ≤ (Dm.iv (cls i) (cls j)).hi
  cuts : ∀ i j k, Distinct3 i j k → cls i ≤ cls j → cls j ≤ cls k →
    ∀ g ∈ findCuts (cls i) (cls j) (cls k) Dm.cuts,
      0 ≤ gval g (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k))

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {cls : ι → ℕ} {x : ι → EuclideanSpace ℝ (Fin 3)}

/-- **The domain of the checker contains the domain of the certificate.** -/
theorem inDomain2_of_source (H : CertHolds2 P Q C xs) (hdom : domOk P C Dm xs = true) (hS : InSource2 P.q C Dm cls x) :
    InDomain2 P C xs cls x := by
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
    exact domGens_nonneg3 P.m Dm (cls i) (cls j) (cls k) (x i) (x j) (x k) (hS.unit i) (hS.unit j) (hS.unit k)
      (hbox i j hd.1 hij) (hbox i k hd.2.1 (le_trans hij hjk)) (hbox j k hd.2.2 hjk) hcut hgm

end Points

end N11.Circ
