module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CAP.Wsos.RootedSum

/-!
# The rooted forms at points of the unit sphere of `ℝ⁴`

A unit vector `r` of `ℝ⁴` is the first vector of an orthonormal basis (`exists_frame4`), so the inner
product of two vectors is the product of their inner products with `r` plus the inner product of
their coordinates along the three further vectors (`frame_coords4`). For points `x j` of the sphere
these coordinates, multiplied by `E`, are the vectors of `ℝ³` to which `rootedV_sum_nonneg` applies:

`rooted_root_nonneg`: for a root `r` and points `x j` of the sphere with classes `cl j`, the sum of
the rooted forms of `r` over all pairs of points is nonnegative. The variables are `E` times the
inner products, as in the checker.
-/

@[expose] public section

namespace CAP.Wsos

open Finset

/-- A unit vector of `ℝ⁴` is the first vector of an orthonormal basis. -/
theorem exists_frame4 (x : EuclideanSpace ℝ (Fin 4)) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)), b 0 = x := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 4)).domRestrict fun _ => x) :=
    ⟨fun _ => hx, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

/-- The inner product in coordinates with respect to a unit vector `x`: its own direction, and three
coordinates orthogonal to it. -/
theorem frame_coords4 (x : EuclideanSpace ℝ (Fin 4)) (hx : ‖x‖ = 1) :
    ∃ p q r : EuclideanSpace ℝ (Fin 4) → ℝ, ∀ y z : EuclideanSpace ℝ (Fin 4),
      inner ℝ y z = inner ℝ x y * inner ℝ x z + p y * p z + q y * q z + r y * r z := by
  obtain ⟨b, hb⟩ := exists_frame4 x hx
  refine ⟨fun y => inner ℝ (b 1) y, fun y => inner ℝ (b 2) y, fun y => inner ℝ (b 3) y, fun y z => ?_⟩
  have h := b.sum_inner_mul_inner y z
  rw [Fin.sum_univ_four, hb] at h
  have e0 : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  have e1 : inner ℝ y (b 1) = inner ℝ (b 1) y := real_inner_comm _ _
  have e2 : inner ℝ y (b 2) = inner ℝ (b 2) y := real_inner_comm _ _
  have e3 : inner ℝ y (b 3) = inner ℝ (b 3) y := real_inner_comm _ _
  rw [e0, e1, e2, e3] at h
  exact h.symm

/-- **The rooted forms of a root on the sphere are positive.** -/
theorem rooted_root_nonneg (P : Params) (gram : List ℕ) (cols : ℕ → List ℕ) (hlen : gram.length ≤ 9)
    (hG : ∀ k < gram.length, GramHolds P (P.d - k) (cols k) (gram.getD k 0))
    {ι : Type*} [Fintype ι] (cl : ι → ℕ) (hcl : ∀ j, cl j < P.q)
    (x : ι → EuclideanSpace ℝ (Fin 4)) (hx : ∀ j, ‖x j‖ = 1) (r : EuclideanSpace ℝ (Fin 4)) (hr : ‖r‖ = 1)
    (E : ℝ) :
    0 ≤ ∑ j, ∑ k, rootedV P E (E * inner ℝ r (x j)) (E * inner ℝ r (x k)) (E * inner ℝ (x j) (x k))
      ⟨gram, cl j, cl k⟩ := by
  obtain ⟨p, q, s, h⟩ := frame_coords4 r hr
  refine rootedV_sum_nonneg P gram cols hlen hG cl hcl E (fun j => E * inner ℝ r (x j))
    (fun j k => E * inner ℝ (x j) (x k)) (fun j => E * p (x j)) (fun j => E * q (x j)) (fun j => E * s (x j)) ?_ ?_
  · intro j k
    unfold AhV
    rw [h (x j) (x k)]
    ring
  · intro j
    have e := h (x j) (x j)
    rw [real_inner_self_eq_norm_sq, hx j, one_pow] at e
    linear_combination E ^ 2 * e

end CAP.Wsos
