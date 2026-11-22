module

public import N11.Analytic.Basic
public import N11.ParallelResearch1.Circ.Graph

/-!
# The theorem for 11 points, analytic part: the theorem of the route in the form of the statement (row A11)

The theorem of the route `N11RG.routeG` is stated for configurations `x : Fin 11 → EuclideanSpace ℝ (Fin 3)` with the
energy `N11.Circ.energy`, a numbering `q : ℕ → Fin 11` and the sum over the points `i < j` with the centres
`τ (min (clsOf q 11 i) (clsOf q 11 j)) (max …)` of the numbers of the points.

* `toE`: the points of Euclidean space with the coordinates of a configuration; `inner_toE`, `norm_toE`,
  `injective_toE`, `circ_energy_toE`: the hypotheses and the energy in the two forms;
* `RouteHyp τ`: the theorem of the route, with the lower bound of the energy of the inner certificate, as a
  hypothesis about a table of centres `τ`;
* `route_confine`: for a configuration of distinct points of the sphere with energy at most `40.59645051` there is
  a relabelling `σ` with `∑_{a<b} (<x_σa, x_σb> - τ_ab)² < 1/9000` (the sum over the pairs of positions), and the
  energy exceeds `40.59644951`.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-! ## Euclidean space -/

/-- The points of Euclidean space with the coordinates of a configuration. -/
noncomputable def toE (x : Fin 11 → Fin 3 → ℝ) (i : Fin 11) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (x i)

theorem inner_toE (x : Fin 11 → Fin 3 → ℝ) (i j : Fin 11) : inner ℝ (toE x i) (toE x j) = ∑ k, x i k * x j k := by
  unfold toE
  simp [PiLp.inner_apply, mul_comm]

theorem norm_toE_sq (x : Fin 11 → Fin 3 → ℝ) (i : Fin 11) : ‖toE x i‖ ^ 2 = ∑ k, x i k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_toE_sub_sq (x : Fin 11 → Fin 3 → ℝ) (i j : Fin 11) :
    ‖toE x i - toE x j‖ ^ 2 = ∑ k, (x i k - x j k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_toE (x : Fin 11 → Fin 3 → ℝ) (hx : OnSphere x) (i : Fin 11) : ‖toE x i‖ = 1 := by
  have h := norm_toE_sq x i
  rw [hx i] at h
  have h0 := norm_nonneg (toE x i)
  nlinarith [sq_nonneg (‖toE x i‖ - 1)]

theorem onSphere_of_norm (x : Fin 11 → Fin 3 → ℝ) (h : ∀ i, ‖toE x i‖ = 1) : OnSphere x := by
  intro i
  rw [← norm_toE_sq, h i]
  norm_num

theorem injective_toE (x : Fin 11 → Fin 3 → ℝ) (hx : Function.Injective x) : Function.Injective (toE x) := by
  intro i j hij
  exact hx (WithLp.toLp_injective 2 hij)

theorem circ_energy_toE (x : Fin 11 → Fin 3 → ℝ) : N11.Circ.energy (toE x) = energy x := by
  unfold N11.Circ.energy energy
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [← norm_toE_sub_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The configuration of the statement with the coordinates of points of Euclidean space. -/
noncomputable def ofE (x : Fin 11 → EuclideanSpace ℝ (Fin 3)) : Fin 11 → Fin 3 → ℝ := fun i k => x i k

theorem toE_ofE (x : Fin 11 → EuclideanSpace ℝ (Fin 3)) : toE (ofE x) = x := by
  funext i
  unfold toE ofE
  rfl

/-! ## The theorem of the route as a hypothesis -/

/-- **The theorem of the route** (`N11RG.routeG` with the lower bound of `N11G.….conf`), for a table of centres `τ`. -/
def RouteHyp (τ : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : Fin 11 → EuclideanSpace ℝ (Fin 3), (∀ i, ‖x i‖ = 1) → Function.Injective x →
    N11.Circ.energy x ≤ 4059645051 / 100000000 →
      ∃ q : ℕ → Fin 11, N11.Circ.InjOn' q 11 ∧ (4059644951 : ℝ) / 100000000 < N11.Circ.energy x ∧
        9 / 1000 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (inner ℝ (x i) (x j)
          - τ (min (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))
              (max (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))) ^ 2
          < 4059645051 / 100000000 - 4059644951 / 100000000

/-- The relabelling of a numbering. -/
noncomputable def permOf (q : ℕ → Fin 11) (hq : N11.Circ.InjOn' q 11) : Equiv.Perm (Fin 11) :=
  Equiv.ofBijective (fun a : Fin 11 => q a.val)
    ((Finite.injective_iff_bijective).mp fun a b h => Fin.ext (hq a.val b.val a.isLt b.isLt h))

theorem permOf_apply (q : ℕ → Fin 11) (hq : N11.Circ.InjOn' q 11) (a : Fin 11) : permOf q hq a = q a.val := rfl

/-- **The confinement from the theorem of the route.** -/
theorem route_confine {τ : ℕ → ℕ → ℝ} (hR : RouteHyp τ) (x : Fin 11 → Fin 3 → ℝ) (hx : OnSphere x)
    (hinj : Function.Injective x) (hE : energy x ≤ 4059645051 / 100000000) :
    ∃ σ : Equiv.Perm (Fin 11), (4059644951 : ℝ) / 100000000 < energy x ∧
      sumP (fun a b => (dot (toN (fun c => x (σ c)) a) (toN (fun c => x (σ c)) b) - τ a b) ^ 2) < 1 / 9000 := by
  have hE' : N11.Circ.energy (toE x) ≤ 4059645051 / 100000000 := by rw [circ_energy_toE]; exact hE
  obtain ⟨q, hq, hlow, hsum⟩ := hR (toE x) (norm_toE x hx) (injective_toE x hinj) hE'
  rw [circ_energy_toE] at hlow
  refine ⟨permOf q hq, hlow, ?_⟩
  set σ := permOf q hq with hσ
  -- the class of the point `σ a` is `a`
  have hcls : ∀ a : Fin 11, N11.Circ.clsOf q 11 (σ a) = a.val := fun a =>
    N11.Circ.clsOf_chosen hq a.isLt
  -- the sum of the route as a sum over the pairs of positions
  set F : Fin 11 → Fin 11 → ℝ := fun i j => if i = j then 0 else (inner ℝ (toE x i) (toE x j)
      - τ (min (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))
          (max (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))) ^ 2 with hF
  have hFs : ∀ i j, F i j = F j i := by
    intro i j
    rw [hF]
    simp only
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), real_inner_comm, min_comm, max_comm]
  have hFd : ∀ i, F i i = 0 := fun i => by rw [hF]; simp
  have h1 := pairsum_comp_perm F hFs hFd σ
  have h2 : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (inner ℝ (toE x i) (toE x j)
          - τ (min (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))
              (max (N11.Circ.clsOf q 11 i) (N11.Circ.clsOf q 11 j))) ^ 2 := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
    rw [hF]
    simp only
    rw [if_neg (ne_of_lt (mem_filter.mp hj).2)]
  have h3 : ∑ a, ∑ b ∈ univ.filter (fun b => a < b), F (σ a) (σ b)
      = sumP (fun a b => (dot (toN (fun c => x (σ c)) a) (toN (fun c => x (σ c)) b) - τ a b) ^ 2) := by
    rw [← sumP_eq_fin]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
    have hab : a < b := (mem_filter.mp hb).2
    have hne : σ a ≠ σ b := fun h => (ne_of_lt hab) (σ.injective h)
    rw [hF]
    simp only
    rw [if_neg hne, hcls a, hcls b, min_eq_left (show (a : ℕ) ≤ b from le_of_lt hab),
      max_eq_right (show (a : ℕ) ≤ b from le_of_lt hab), inner_toE,
      dot_toN]
  rw [← h2, ← h1, h3] at hsum
  linarith

end N11.Analytic
