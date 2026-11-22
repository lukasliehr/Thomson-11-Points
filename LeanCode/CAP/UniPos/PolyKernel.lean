module

public import CAP.UniPos.Kernel

/-!
# E3, sign of a polynomial on an interval: the checker (`Init` only)

**Statement.** Let `p(t) = ∑ d ≤ n, P d * t ^ d` with integers `P d`, and let `a ≤ b` be dyadic
numbers. Then `p ≥ 0` on `[a, b]` (`st = 0`), respectively `p > 0` on `[a, b]` (`st = 1`).

**Witness.** Cut points `a = t_0 < t_1 < … < t_m = b`. A point is stored as a natural number `c`
and stands for `(c - off) / 2 ^ s`.

**Method.** For a pair of points `c`, `c'` the variable is `t = (M⁺ - M⁻) / L` with the linear
forms `L = 2 ^ s * (1 + y)`, `M⁺ = c + c' * y` and `M⁻ = off * (1 + y)`, `y ≥ 0`; it runs from the
point `c` (for `y = 0`) towards the point `c'`. The polynomial

  `B(y) = ∑ d, P d * (M⁺ - M⁻) ^ d * L ^ (n - d)`

equals `L ^ n * p(t)`. If all coefficients of `B` are nonnegative, then `p ≥ 0` between the two
points, and if moreover its constant coefficient is positive, then `p > 0` there. The checker
tests every pair of consecutive cut points, and the last pair also in the reverse order, which
covers the point `b`.

**Arithmetic.** As in `CAP.UniPos.Kernel`: a polynomial in `y` with natural coefficients is the
number obtained at `y = 2 ^ V`, a polynomial with integer coefficients is a pair (positive part,
negative part), `B` is computed by Horner's rule with the three linear forms, and the same
program with `V = 0` bounds the coefficients.

**Data.** `Pp` has the slot width `W`; slot `d` is `P d + 2 ^ (aH - 1)`. The cuts are the list
`[c_1, …, c_m]`, and `c_0` is given separately.

The checker is bit-exact with `certgen/unipos_poly.py`.
-/

@[expose] public section

namespace CAP.UniPos

/-- Parameters of the sign condition. -/
structure PParams where
  /-- the polynomial has degree at most `n` -/
  n : Nat
  /-- slot width of the data `Pp` -/
  W : Nat
  /-- the coefficient `d` is slot `d` of `Pp` minus `2 ^ (aH - 1)` -/
  aH : Nat
  /-- slot width of the polynomials in `y` -/
  V : Nat
  /-- the point `c` stands for `(c - off) / 2 ^ s` -/
  s : Nat
  /-- the offset of the points -/
  off : Nat
  /-- `0` for `p ≥ 0`, `1` for `p > 0` -/
  st : Nat

/-- `X * (off * (1 + y))` for a polynomial `X` at `y = 2 ^ V`. -/
def mulOff (V off X : Nat) : Nat := Nat.mul off (Nat.add X (Nat.shiftLeft X V))

/-- Horner's rule for `B`. With `cnt` coefficients left, the next coefficient has the index
`cnt - 1`; the state is the pair of the partial sum and the power of `L`. -/
noncomputable def hornerG (P : PParams) (V Pp c c' : Nat) (cnt : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun Sp Sn _ => (Sp, Sn))
    (fun k ih Sp Sn Pw =>
      ih (Nat.add (Nat.add (mulM V c c' Sp) (mulOff V P.off Sn)) (Nat.mul (slot P.W Pp k) Pw))
        (Nat.add (Nat.add (mulM V c c' Sn) (mulOff V P.off Sp))
          (Nat.mul (Nat.shiftLeft 1 (Nat.sub P.aH 1)) Pw))
        (mulL2 V P.s Pw))
    cnt

/-- The test of the pair of points `c`, `c'`: the sums of the coefficients of both parts of `B`
are below `2 ^ (V - 1)`, the coefficients of `B` are nonnegative, and its constant coefficient is
at least `st`. -/
noncomputable def pieceOk (P : PParams) (Pp c c' : Nat) : Bool :=
  Nat.blt (hornerG P 0 Pp c c' (Nat.succ P.n) 0 0 1).1 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  Nat.blt (hornerG P 0 Pp c c' (Nat.succ P.n) 0 0 1).2 (Nat.shiftLeft 1 (Nat.sub P.V 1)) &&
  geTest P.V (Nat.add P.n 2) (hornerG P P.V Pp c c' (Nat.succ P.n) 0 0 1).1
    (hornerG P P.V Pp c c' (Nat.succ P.n) 0 0 1).2 &&
  Nat.ble (Nat.add (slot P.V (hornerG P P.V Pp c c' (Nat.succ P.n) 0 0 1).2 0) P.st)
    (slot P.V (hornerG P P.V Pp c c' (Nat.succ P.n) 0 0 1).1 0)

/-- The loop over the cuts; `prev` is the previous cut and `prev2` the one before it. The cuts
increase. At the end the last pair is tested in the reverse order. -/
noncomputable def cutsG (P : PParams) (Pp : Nat) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun prev prev2 => pieceOk P Pp prev prev2)
    (fun c _ ih prev _ => Nat.blt prev c && pieceOk P Pp prev c && ih c prev)

/-- The checker of the sign of a polynomial on `[c0, last cut]`. -/
noncomputable def checkPoly (P : PParams) (Pp c0 : Nat) (cuts : List Nat) : Bool :=
  Nat.ble 1 P.V && Nat.ble P.st 1 && cutsG P Pp cuts c0 c0

end CAP.UniPos
