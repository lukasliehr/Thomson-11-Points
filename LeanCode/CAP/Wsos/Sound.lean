module

public import CAP.Wsos.Cheb

/-!
# Soundness of the checker of a triple type

`checkTy_sound`: if `CAP.Wsos.checkTy P T = true` and the layout of `P` is injective on the
monomials of degree at most `D`, then for all real `x, y, z` in `[-1, 1]` at which the generators of
all weights of `T` are nonnegative,

    c2p - c2n ≤ lamV P T (2 ^ m) (ρᵤ x + cᵤ) (ρᵥ y + cᵥ) (ρₜ z + cₜ),

where `lamV` is the left-hand side of the identity of the triple type, defined from the shares and
the rooted forms of the data in `CAP.Wsos.Value`.

The proof: the number of the residual stands for a polynomial `RP = lamV - c - WP`, where `WP` is
a sum of products of generators with sums of squares (`weightsGo_exists`); the checker compares
`2 ^ D * RP` with a Chebyshev combination modulo `2 ^ M`; both sides have bounded coefficients, so
they are equal as polynomials (`kron_zero`); on the cube the Chebyshev combination is nonnegative.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

/-- The value of a polynomial at a real point. -/
noncomputable def rv (x y z : ℝ) : Poly →+* ℝ := eval₂Hom (Int.castRingHom ℝ) ![x, y, z]

theorem rv_X0 (x y z : ℝ) : rv x y z (X 0) = x := by simp [rv]

theorem rv_X1 (x y z : ℝ) : rv x y z (X 1) = y := by simp [rv]

theorem rv_X2 (x y z : ℝ) : rv x y z (X 2) = z := by simp [rv]

theorem rv_EP (P : Params) (x y z : ℝ) : rv x y z (EP P) = (2 : ℝ) ^ P.m := by
  unfold EP
  rw [map_pow, map_ofNat]

theorem rv_natC (x y z : ℝ) (n : ℕ) : rv x y z (C ((n : ℕ) : ℤ)) = (n : ℝ) := by
  rw [C_natCast', map_natCast]

/-! ## The conditions of the checker -/

theorem nat_beq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem paramsOk_iff (P : Params) : paramsOk P = true ↔
    1 ≤ P.k1 ∧ P.k1 ≤ P.k2 ∧ P.k2 * P.D < P.slots ∧ P.D = 2 * P.d ∧ 1 ≤ P.wG ∧ 1 ≤ P.wP ∧ 1 ≤ P.w0 ∧ P.w0 ≤ P.W := by
  unfold paramsOk
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, nat_beq_iff, and_assoc]
  rfl

theorem rootsOk_iff (P : Params) : ∀ roots : List RootUse,
    rootsOk P roots = true ↔ ∀ Ru ∈ roots, Ru.gram.length ≤ P.d + 1
  | [] => by simp [rootsOk]
  | Ru :: roots => by
    have e : rootsOk P (Ru :: roots) = (Nat.ble (len Ru.gram) (Nat.succ P.d) && rootsOk P roots) := rfl
    rw [e, Bool.and_eq_true, Nat.ble_eq, len_eq, rootsOk_iff P roots]
    simp

theorem shareOk_iff (P : Params) (S : Share) : shareOk P S = true ↔
    1 ≤ S.mult ∧ S.negs.length = S.negm.length ∧ ∀ Ru ∈ S.roots, Ru.gram.length ≤ P.d + 1 := by
  unfold shareOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, nat_beq_iff, len_eq, len_eq, rootsOk_iff, and_assoc]

theorem flags_iff (P : Params) (T : Ty) : flags P T = true ↔
    paramsOk P = true ∧ boxOk P T.bu = true ∧ boxOk P T.bv = true ∧ boxOk P T.bt = true ∧ shareOk P T.s1 = true
      ∧ shareOk P T.s2 = true ∧ shareOk P T.s3 = true ∧ T.r1.gram.length ≤ P.d + 1 ∧ T.r2.gram.length ≤ P.d + 1
      ∧ T.r3.gram.length ≤ P.d + 1 ∧ weightsOk P T.weights = true := by
  unfold flags
  simp only [Bool.and_eq_true, Nat.ble_eq, len_eq, and_assoc]

/-! ## The residual -/

/-- The bound of the checker for the coefficients of the residual. -/
theorem bound_eq (P : Params) (T : Ty) (sp sn : ℕ) :
    bound P T sp sn = 2 ^ P.D * (fact P.d * (T.s2.mult * T.s3.mult * nShare P T.s1 + T.s1.mult * T.s3.mult * nShare P T.s2
        + T.s1.mult * T.s2.mult * nShare P T.s3)
      + 2 ^ P.aF * (2 * (T.s1.mult * T.s2.mult * T.s3.mult) * (3 * nRooted P)) + T.c2p + T.c2n + nWeightsGo P T.weights 0)
      + (sp + sn) * 3 ^ P.D := by
  unfold bound
  show ((fact P.d * (T.s2.mult * T.s3.mult * nShare P T.s1 + T.s1.mult * T.s3.mult * nShare P T.s2
        + T.s1.mult * T.s2.mult * nShare P T.s3)
      + (2 * (T.s1.mult * T.s2.mult * T.s3.mult) * (3 * nRooted P)) <<< P.aF + T.c2p + T.c2n + nWeightsGo P T.weights 0) <<< P.D)
      + (sp + sn) * 3 ^ P.D = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

/-- **Soundness of the checker of a triple type.** -/
theorem checkTy_sound (P : Params) (T : Ty) (hL : LayoutInj P.D P.k1 P.k2) (h : checkTy P T = true)
    (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1)
    (hg : ∀ w ∈ T.weights, ∀ g ∈ w.gens,
      0 ≤ genV ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z) g) :
    ((T.c2p : ℝ) - (T.c2n : ℝ)) ≤ lamV P T ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z) := by
  -- the conditions
  set pM := Nat.shiftLeft 1 (Nat.mul P.W P.slots) with hpM
  set mM := Nat.sub pM 1 with hmM
  have hM : Mod P pM mM := mod_of P
  have h1 : checkK P T pM mM (chebSum P T.Np) (chebSum P T.Nn) = true := h
  unfold checkK at h1
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, nat_beq_iff, Nat.ble_eq] at h1
  obtain ⟨⟨⟨hflags, hbound⟩, hnum⟩, hsum⟩ := h1
  obtain ⟨hpar, hbu, hbv, hbt, hs1, hs2, hs3, hr1, hr2, hr3, hwok⟩ := (flags_iff P T).mp hflags
  obtain ⟨hk1, hk, hslots, hD, hG, hP, hw1, hw⟩ := (paramsOk_iff P).mp hpar
  obtain ⟨_, hl1, hR1⟩ := (shareOk_iff P T.s1).mp hs1
  obtain ⟨_, hl2, hR2⟩ := (shareOk_iff P T.s2).mp hs2
  obtain ⟨_, hl3, hR3⟩ := (shareOk_iff P T.s3).mp hs3
  have hdD : P.d ≤ P.D := by omega
  -- the variables
  set u := aff pM mM T.bu (Nat.shiftLeft 1 P.W) with hu_def
  set v := aff pM mM T.bv (Nat.shiftLeft 1 (Nat.mul P.W P.k1)) with hv_def
  set t := aff pM mM T.bt (Nat.shiftLeft 1 (Nat.mul P.W P.k2)) with ht_def
  set uP : Poly := affV T.bu (X 0) with huP
  set vP : Poly := affV T.bv (X 1) with hvP
  set tP : Poly := affV T.bt (X 2) with htP
  have hu : Rep P u uP := aff_rep hM T.bu (rep_X0 P)
  have hv : Rep P v vP := aff_rep hM T.bv (rep_X1 P)
  have ht : Rep P t tP := aff_rep hM T.bt (rep_X2 P)
  have bu : Bd uP (2 ^ P.m) 1 := aff_bd T.bu hbu 0
  have bv : Bd vP (2 ^ P.m) 1 := aff_bd T.bv hbv 1
  have bt : Bd tP (2 ^ P.m) 1 := aff_bd T.bt hbt 2
  -- the parts of the residual
  have hsh1 := shareVal_rep hM hu hdD hG T.s1 hl1 hR1 (fact P.d)
  have hsh2 := shareVal_rep hM hv hdD hG T.s2 hl2 hR2 (fact P.d)
  have hsh3 := shareVal_rep hM ht hdD hG T.s3 hl3 hR3 (fact P.d)
  have hro1 := rootedVal_rep hM hu hv ht hdD T.r1 hr1
  have hro2 := rootedVal_rep hM hu ht hv hdD T.r2 hr2
  have hro3 := rootedVal_rep hM hv ht hu hdD T.r3 hr3
  obtain ⟨WP, hrW, hbW, hnW⟩ := weightsGo_exists hM hL hk1 hk hslots hw1 hw hD hu hv ht bu bv bt T.weights hwok
  set RP : Poly := lamV P T (EP P) uP vP tP - C (((T.c2p : ℕ) : ℤ) - ((T.c2n : ℕ) : ℤ)) - WP with hRP
  have hres : Rep P (residual P T pM mM) RP := by
    have hA := (((Rep.smul (T.s2.mult * T.s3.mult) hsh1).add (Rep.smul (T.s1.mult * T.s3.mult) hsh2)).add
      (Rep.smul (T.s1.mult * T.s2.mult) hsh3)).add (Rep.natCast T.c2n)
    have hB := ((((Rep.smul (2 * (T.s1.mult * T.s2.mult * T.s3.mult)) (((hro1.add hro2).add hro3).land hM)).shiftLeft
      P.aF).add (Rep.natCast T.c2p))).add (hrW 0 0 Rep.zero)
    refine (hA.subM hM hB).congr ?_
    rw [hRP]
    unfold lamV
    rw [C_two_pow, map_sub]
    simp only [C_natCast']
    push_cast
    ring
  have bRP : Bd RP (fact P.d * (T.s2.mult * T.s3.mult * nShare P T.s1 + T.s1.mult * T.s3.mult * nShare P T.s2
        + T.s1.mult * T.s2.mult * nShare P T.s3)
      + 2 ^ P.aF * (2 * (T.s1.mult * T.s2.mult * T.s3.mult) * (3 * nRooted P)) + T.c2p + T.c2n
      + nWeightsGo P T.weights 0) P.D := by
    have b1 := shareV_bd hD hG hP bu T.s1 hl1 hR1
    have b2 := shareV_bd hD hG hP bv T.s2 hl2 hR2
    have b3 := shareV_bd hD hG hP bt T.s3 hl3 hR3
    have c1 := rootedV_bd hD hG bu bv bt T.r1 hr1
    have c2 := rootedV_bd hD hG bu bt bv T.r2 hr2
    have c3 := rootedV_bd hD hG bv bt bu T.r3 hr3
    have hlam : Bd (lamV P T (EP P) uP vP tP)
        (fact P.d * (T.s2.mult * T.s3.mult * nShare P T.s1 + T.s1.mult * T.s3.mult * nShare P T.s2
          + T.s1.mult * T.s2.mult * nShare P T.s3)
        + 2 ^ P.aF * (2 * (T.s1.mult * T.s2.mult * T.s3.mult) * (3 * nRooted P))) P.D := by
      unfold lamV
      have s1 := ((Bd.smul (T.s2.mult * T.s3.mult) b1).add (Bd.smul (T.s1.mult * T.s3.mult) b2)).add
        (Bd.smul (T.s1.mult * T.s2.mult) b3)
      have s2 := Bd.smul (fact P.d) s1
      have r1 := (Bd.smul (2 * (T.s1.mult * T.s2.mult * T.s3.mult)) ((c1.add c2).add c3))
      have r2 := (bd_two_pow P.aF).mul r1
      rw [zero_add] at r2
      refine ((s2.sub r2).mono (le_of_eq ?_) le_rfl).congr ?_
      · ring
      · simp only [C_natCast']
        ring
    have hc : Bd (C (((T.c2p : ℕ) : ℤ) - ((T.c2n : ℕ) : ℤ)) : Poly) (T.c2p + T.c2n) P.D := by
      have := ((Bd.natCast T.c2p).sub (Bd.natCast T.c2n)).mono le_rfl (Nat.zero_le P.D)
      rwa [← map_sub] at this
    exact (hlam.sub hc).sub hbW |>.mono (le_of_eq (by ring)) le_rfl
  -- the Chebyshev combination
  set ChP : Poly := chOutV P.wN (X 0) (X 1) (X 2) (P.D + 1) 0 T.Np with hChP
  set ChN : Poly := chOutV P.wN (X 0) (X 1) (X 2) (P.D + 1) 0 T.Nn with hChN
  have hcp : Rep P (chebVal P pM mM T.Np) ChP := chebVal_rep hM T.Np
  have hcn : Rep P (chebVal P pM mM T.Nn) ChN := chebVal_rep hM T.Nn
  have bcp : Bd ChP (chebSum P T.Np * 3 ^ P.D) P.D := by
    rw [chebSum_eq]; exact chOutV_bd P.wN (P.D + 1) 0 T.Np P.D (by omega)
  have bcn : Bd ChN (chebSum P T.Nn * 3 ^ P.D) P.D := by
    rw [chebSum_eq]; exact chOutV_bd P.wN (P.D + 1) 0 T.Nn P.D (by omega)
  -- the two polynomials are equal
  have hF0 : C ((2 : ℤ) ^ P.D) * RP - (ChP - ChN) = 0 := by
    have b : Bd (C ((2 : ℤ) ^ P.D) * RP - (ChP - ChN)) (bound P T (chebSum P T.Np) (chebSum P T.Nn)) P.D := by
      have b1 : Bd (C ((2 : ℤ) ^ P.D) * RP) (2 ^ P.D * (fact P.d * (T.s2.mult * T.s3.mult * nShare P T.s1
          + T.s1.mult * T.s3.mult * nShare P T.s2 + T.s1.mult * T.s2.mult * nShare P T.s3)
        + 2 ^ P.aF * (2 * (T.s1.mult * T.s2.mult * T.s3.mult) * (3 * nRooted P)) + T.c2p + T.c2n
        + nWeightsGo P T.weights 0)) P.D := by
        have := (bd_two_pow P.D).mul bRP
        rw [zero_add, ← C_two_pow] at this
        exact this
      refine (b1.sub (bcp.sub bcn)).mono (le_of_eq ?_) le_rfl
      rw [bound_eq]
      ring
    have hW1 : 1 ≤ P.W := le_trans hw1 hw
    have hb' : bound P T (chebSum P T.Np) (chebSum P T.Nn) < 2 ^ (P.W - 1) := by
      have : Nat.shiftLeft 1 (Nat.pred P.W) = 2 ^ (P.W - 1) := by
        show 1 <<< (P.W - 1) = _
        rw [Nat.one_shiftLeft]
      rwa [this] at hbound
    refine kron_zero P hL hk1 hk hslots hW1 b hb' ?_
    have e1 : Rep P (Nat.land (Nat.shiftLeft (residual P T pM mM) P.D) mM) (C ((2 : ℤ) ^ P.D) * RP) :=
      (hres.shiftLeft P.D).land hM
    have e2 : Rep P (Nat.land (subM pM mM (chebVal P pM mM T.Np) (chebVal P pM mM T.Nn)) mM) (ChP - ChN) :=
      (hcp.subM hM hcn).land hM
    rw [hnum] at e1
    unfold Rep at e1 e2
    rw [map_sub]
    exact Int.modEq_zero_iff_dvd.mpr (Int.modEq_iff_dvd.mp (e1.symm.trans e2) |> fun hdvd => by
      have : ev P (C ((2 : ℤ) ^ P.D) * RP) - ev P (ChP - ChN) = -(ev P (ChP - ChN) - ev P (C ((2 : ℤ) ^ P.D) * RP)) := by ring
      rw [this]
      exact (dvd_neg).mpr hdvd)
  -- the values at the real point
  set ρ := rv x y z with hρ
  have hρE : ρ (EP P) = (2 : ℝ) ^ P.m := rv_EP P x y z
  have hρu : ρ uP = affV T.bu x := by rw [huP, map_affV, hρ, rv_X0]
  have hρv : ρ vP = affV T.bv y := by rw [hvP, map_affV, hρ, rv_X1]
  have hρt : ρ tP = affV T.bt z := by rw [htP, map_affV, hρ, rv_X2]
  have hWnn : 0 ≤ ρ WP := by
    refine hnW ρ fun w hw' g hg' => ?_
    rw [map_genV, hρE, hρu, hρv, hρt]
    exact hg w hw' g hg'
  have hlamρ : ρ (lamV P T (EP P) uP vP tP)
      = lamV P T ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z) := by
    rw [map_lamV, hρE, hρu, hρv, hρt]
  have hChPρ : ρ ChP = chOutV P.wN x y z (P.D + 1) 0 T.Np := by
    rw [hChP, map_chOutV, hρ, rv_X0, rv_X1, rv_X2]
  have hChNρ : ρ ChN = chOutV P.wN x y z (P.D + 1) 0 T.Nn := by
    rw [hChN, map_chOutV, hρ, rv_X0, rv_X1, rv_X2]
  have hRρ : (2 : ℝ) ^ P.D * ρ RP = chOutV P.wN x y z (P.D + 1) 0 T.Np - chOutV P.wN x y z (P.D + 1) 0 T.Nn := by
    have := congrArg ρ hF0
    rw [map_sub, map_sub, map_mul, map_zero, hChPρ, hChNρ, C_two_pow, map_pow, map_ofNat] at this
    linarith
  have hlow := chOutV_lower hx hy hz P.wN P.D T.Np
  have hupp := chOutV_upper hx hy hz P.wN (P.D + 1) T.Nn
  have hsumR : ((dsT P.wN (tet (P.D + 1)) T.Np : ℕ) : ℝ) + ((dsT P.wN (tet (P.D + 1)) T.Nn : ℕ) : ℝ)
      ≤ 2 * ((slot P.wN T.Np 0 : ℕ) : ℝ) := by
    rw [chebSum_eq, chebSum_eq] at hsum
    rw [slot_zero]
    exact_mod_cast hsum
  have hRnn : 0 ≤ ρ RP := by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ P.D * ρ RP := by rw [hRρ]; linarith
    have h3 : (0 : ℝ) < (2 : ℝ) ^ P.D := by positivity
    exact nonneg_of_mul_nonneg_right h2 h3
  have hRPρ : ρ RP = lamV P T ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z)
      - ((T.c2p : ℝ) - (T.c2n : ℝ)) - ρ WP := by
    rw [hRP, map_sub, map_sub, hlamρ]
    simp only [map_sub, C_natCast', map_natCast]
  linarith

/-- The statement of a triple type: the left-hand side of its identity is at least its constant at
every point of the cube at which the generators of its weights are nonnegative. -/
def TyHolds (P : Params) (T : Ty) : Prop :=
  ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
    (∀ w ∈ T.weights, ∀ g ∈ w.gens, 0 ≤ genV ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z) g) →
    ((T.c2p : ℝ) - (T.c2n : ℝ)) ≤ lamV P T ((2 : ℝ) ^ P.m) (affV T.bu x) (affV T.bv y) (affV T.bt z)

theorem checkTy_holds {P : Params} {T : Ty} (hL : LayoutInj P.D P.k1 P.k2) (h : checkTy P T = true) :
    TyHolds P T := checkTy_sound P T hL h

end CAP.Wsos
