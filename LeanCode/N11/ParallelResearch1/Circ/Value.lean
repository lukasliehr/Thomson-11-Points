module

public import CAP.Wsos.Value
public import N11.ParallelResearch1.Circ.Kernel

/-!
# What the data of a triple type mean, with the kernels of the circle

The expressions of `CAP/Wsos/Value.lean` that contain the kernels, written with the kernels of the circle
`R 0 = 1`, `R 1 = A`, `R (k + 1) = 2 A R k - W R (k - 1)`: the kernel `qV2`, the rooted form `rootedV2` (without
the factors `d! / k!`) and the left-hand side `lamV2` of the identity of a triple type (without the factor
`d!`). They are defined over an arbitrary commutative ring, and a homomorphism of rings maps them to the
expressions over its target.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

variable {A : Type*} [CommRing A]

/-- The coefficient of `A * R k` in the recurrence: `1` for `k = 0` and `2` otherwise. -/
def cf (k : ℕ) : ℕ := cond (Nat.beq k 0) 1 2

theorem cf_zero : cf 0 = 1 := rfl

theorem cf_succ (k : ℕ) : cf (k + 1) = 2 := rfl

theorem cf_le (k : ℕ) : cf k ≤ 2 := by
  cases k with
  | zero => decide
  | succ k => exact le_refl 2

/-- The pair `(R (k - 1), R k)` of the kernels of the circle. -/
def qPair2 (Ah Wh : A) : ℕ → A × A
  | 0 => (0, 1)
  | k + 1 => ((qPair2 Ah Wh k).2, ((cf k : ℕ) : A) * Ah * (qPair2 Ah Wh k).2 - Wh * (qPair2 Ah Wh k).1)

/-- The kernel `R k` of the circle, homogeneous. -/
def qV2 (Ah Wh : A) (k : ℕ) : A := (qPair2 Ah Wh k).2

/-- A rooted form with the kernels of the circle, homogeneous of degree `2 * d`. -/
noncomputable def rootedV2 (P : Params) (E w1 w2 w3 : A) (R : Rooted) : A :=
  ∑ k ∈ range R.gram.length, qV2 (AhV E w1 w2 w3) (WhV E w1 w2) k
    * bilV P.wG E w1 w2 (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c)

/-- The left-hand side of the identity of a triple type, in the unit of the checker. -/
noncomputable def lamV2 (P : Params) (T : Ty) (E u v t : A) : A :=
  (((T.s2.mult * T.s3.mult : ℕ) : A) * shareV P E u T.s1
      + ((T.s1.mult * T.s3.mult : ℕ) : A) * shareV P E v T.s2 + ((T.s1.mult * T.s2.mult : ℕ) : A) * shareV P E t T.s3)
    - 2 ^ P.aF * ((2 * (T.s1.mult * T.s2.mult * T.s3.mult) : ℕ) : A)
      * (rootedV2 P E u v t T.r1 + rootedV2 P E u t v T.r2 + rootedV2 P E v t u T.r3)

section Map

variable {A' : Type*} [CommRing A'] (φ : A →+* A')

theorem map_qPair2 (Ah Wh : A) : ∀ k, (φ (qPair2 Ah Wh k).1, φ (qPair2 Ah Wh k).2) = qPair2 (φ Ah) (φ Wh) k
  | 0 => by simp [qPair2]
  | k + 1 => by
    have h := map_qPair2 Ah Wh k
    rw [Prod.ext_iff] at h
    simp only [qPair2, map_sub, map_mul, map_natCast]
    rw [← h.1, ← h.2]

theorem map_qV2 (Ah Wh : A) (k : ℕ) : φ (qV2 Ah Wh k) = qV2 (φ Ah) (φ Wh) k := by
  have h := map_qPair2 φ Ah Wh k
  rw [Prod.ext_iff] at h
  exact h.2

theorem map_rootedV2 (P : Params) (E w1 w2 w3 : A) (R : Rooted) :
    φ (rootedV2 P E w1 w2 w3 R) = rootedV2 P (φ E) (φ w1) (φ w2) (φ w3) R := by
  simp [rootedV2, map_qV2, map_AhV, map_WhV, map_bilV]

theorem map_lamV2 (P : Params) (T : Ty) (E u v t : A) :
    φ (lamV2 P T E u v t) = lamV2 P T (φ E) (φ u) (φ v) (φ t) := by
  simp [lamV2, map_shareV, map_rootedV2, map_ofNat]

end Map

end N11.Circ
