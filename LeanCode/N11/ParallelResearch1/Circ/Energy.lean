module

public import N11.ParallelResearch1.Circ.Minorant

/-!
# The theorem of a typed certificate on the two-sphere

Let `x i` be distinct points of the unit sphere of `ℝ³` with classes, in the domain of a typed certificate
(`InSource2`: the inner product of every pair lies in the interval of its pair type). The potential of a pair of
points with the classes `a`, `b` and the inner product `t` is

    potV sP sg a b t = 1 / √(2 - 2 t) - pen t,

where `pen` is the polynomial of the pair type (`Pen.val`); `1 / √(2 - 2 t)` is `1 / ‖x i - x j‖`.

`energy2_gt`: let the data of the certificate satisfy `CertHolds2` (the statements of the checkers `checkTy2` and
`gramOk` and the conditions on the tables), `domOk`, `Minorant2` (the sign conditions) and `boundOk2`. Then the
sum of the potentials over the pairs of points exceeds `tp / tq`.

`energy2_gt_fin`: the same with the sum over the pairs `i < j` of `Fin n`.
`coulomb2_gt_fin`: if no pair type has a polynomial `pen`, the Coulomb energy `∑ i < j, 1 / ‖x i - x j‖`
exceeds `tp / tq`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-- The potential of a pair of points with the classes `a`, `b` at the inner product `t`. -/
noncomputable def potV (sP : ℕ) (sg : ℕ → ℕ → Sign2) (a b : ℕ) (t : ℝ) : ℝ :=
  1 / Real.sqrt (2 - 2 * t)
    - (sg (min a b) (max a b)).pen.val (2 ^ sP * ((sg (min a b) (max a b)).sc : ℝ)) t

theorem potV_comm (sP : ℕ) (sg : ℕ → ℕ → Sign2) (a b : ℕ) (t : ℝ) : potV sP sg b a t = potV sP sg a b t := by
  unfold potV
  rw [min_comm, max_comm]

section Points

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP : ℕ} {sg : ℕ → ℕ → Sign2}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ} {x : ι → EuclideanSpace ℝ (Fin 3)}

omit [DecidableEq ι] in
/-- The pair polynomial of two points is at most the potential, in the unit of the checker. -/
theorem pairH2_le (hmin : Minorant2 P C Dm sP sg) (hS : InSource2 P.q C Dm cls x) {i j : ι} (hij : i ≠ j) :
    pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j)
      ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) := by
  have L := hS.lab
  have key : ∀ i j : ι, i ≠ j → cls i ≤ cls j →
      pairH P C (cls i) (cls j) (wv3 P.m x i j)
        ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP)
          * (1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
            - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j))) := by
    intro i j hij hle
    obtain ⟨hlo, hhi⟩ := hS.iv i j hij hle
    have ht1 : inner ℝ (x i) (x j) < 1 :=
      (inner_lt_one_iff_real_of_norm_eq_one (hS.unit i) (hS.unit j)).mpr fun e => hij (hS.inj e)
    have hH := hmin _ (L.lt i) _ (L.lt j) hle (L.pcnt_pos hij) _ hlo hhi ht1
    have h2 : spolyV P.wP (1 : ℝ) (inner ℝ (x i) (x j)) P.D (C.H (cls i) (cls j))
        ≤ 2 ^ sP * (1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
          - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j))) := by
      have hp : (0 : ℝ) < 2 ^ sP := by positivity
      have h3 : spolyV P.wP (1 : ℝ) (inner ℝ (x i) (x j)) P.D (C.H (cls i) (cls j)) / 2 ^ sP
          ≤ 1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
            - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j)) := by
        linarith
      rw [div_le_iff₀ hp] at h3
      linarith
    have h3 : (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * spolyV P.wP (1 : ℝ) (inner ℝ (x i) (x j)) P.D (C.H (cls i) (cls j)))
        ≤ (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * (2 ^ sP * (1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
          - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    have e : (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * (1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
          - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j)))
        = (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * (2 ^ sP * (1 / Real.sqrt (2 - 2 * inner ℝ (x i) (x j))
          - (sg (cls i) (cls j)).pen.val (2 ^ sP * ((sg (cls i) (cls j)).sc : ℝ)) (inner ℝ (x i) (x j))))) := by
      rw [pow_add, pow_add, pow_mul]
      ring
    unfold pairH wv3
    rw [spolyV_hom, e]
    exact h3
  rcases le_total (cls i) (cls j) with hle | hle
  · unfold potV
    rw [min_eq_left hle, max_eq_right hle]
    exact key i j hij hle
  · have h := key j i (Ne.symm hij) hle
    rw [wv3_comm P.m x i j, real_inner_comm (x i) (x j)] at h
    unfold potV
    rw [min_eq_right hle, max_eq_left hle]
    exact h

/-- **The sum of the potentials of points in the domain of a typed certificate exceeds `tp / tq`.** The sum
runs over the ordered pairs of distinct points, hence the factor `1 / 2`. -/
theorem energy2_gt {M tp tq : ℕ} (H : CertHolds2 P Q C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant2 P C Dm sP sg) (hb : boundOk2 P C xs sP M tp tq = true) (hS : InSource2 P.q C Dm cls x) :
    (tp : ℝ) / tq < (∑ i, ∑ j, if i ≠ j then potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) else 0) / 2 := by
  have hD := inDomain2_of_source H hdom hS
  have hT : dsum3 (fun i j k => tyC2 P Q C (typeOf xs (cls i) (cls j) (cls k)))
      ≤ 3 * (∑ i, ∑ j, if i ≠ j then
          pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j) else 0)
        + 6 * ∑ i, rootS2 P C (cls i) Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) :=
    typed_bound2 H hD
  have hsum : (∑ i, ∑ j, if i ≠ j then
        pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv3 P.m x i j) else 0)
      ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP)
        * ∑ i, ∑ j, if i ≠ j then potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) else 0 := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_pos hij, if_pos hij]
      exact pairH2_le hmin hS hij
  refine boundOk2_sound H hb hS.lab _ ?_
  have e : 6 * (2 : ℝ) ^ (P.m * P.D + P.aP + sP)
        * ((∑ i, ∑ j, if i ≠ j then potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) else 0) / 2)
      = 3 * ((2 : ℝ) ^ (P.m * P.D + P.aP + sP)
        * ∑ i, ∑ j, if i ≠ j then potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) else 0) := by ring
  rw [e]
  linarith

end Points

/-- The same for points with the indices `Fin n`, with the sum over the pairs `i < j`. -/
theorem energy2_gt_fin {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq n : ℕ}
    {sg : ℕ → ℕ → Sign2} {cls : Fin n → ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (H : CertHolds2 P Q C xs)
    (hdom : domOk P C Dm xs = true) (hmin : Minorant2 P C Dm sP sg) (hb : boundOk2 P C xs sP M tp tq = true)
    (hS : InSource2 P.q C Dm cls x) :
    (tp : ℝ) / tq < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)) := by
  have h := energy2_gt H hdom hmin hb hS
  rw [CAP.ThreePoint.sum_ne_eq_two_mul_sum_lt (fun i j => potV sP sg (cls i) (cls j) (inner ℝ (x i) (x j)))
    (fun i j => by rw [potV_comm, real_inner_comm]), mul_div_cancel_left₀ _ (two_ne_zero)] at h
  exact h

/-- The Coulomb potential of two points of the unit sphere. -/
theorem one_div_dist {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    1 / Real.sqrt (2 - 2 * inner ℝ x y) = 1 / ‖x - y‖ := by
  have hn : ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [norm_sub_sq_real, hx, hy]
    ring
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

/-- **The Coulomb energy of points in the domain of a typed certificate without polynomials `pen` exceeds
`tp / tq`.** -/
theorem coulomb2_gt_fin {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq n q : ℕ}
    {l : List Sign2} {cls : Fin n → ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (H : CertHolds2 P Q C xs)
    (hdom : domOk P C Dm xs = true) (hmin : Minorant2 P C Dm sP (signOf2 q l)) (hpen : pensZero l = true)
    (hb : boundOk2 P C xs sP M tp tq = true) (hS : InSource2 P.q C Dm cls x) :
    (tp : ℝ) / tq < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ := by
  have h := energy2_gt_fin H hdom hmin hb hS
  have e : ∀ i j : Fin n, potV sP (signOf2 q l) (cls i) (cls j) (inner ℝ (x i) (x j)) = 1 / ‖x i - x j‖ := by
    intro i j
    unfold potV
    rw [pensZero_val hpen, sub_zero, one_div_dist (hS.unit i) (hS.unit j)]
  simp only [e] at h
  exact h

end N11.Circ
