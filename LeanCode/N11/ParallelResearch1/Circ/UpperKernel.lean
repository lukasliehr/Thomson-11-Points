module

public import CAP.Wsos.CertKernel

/-!
# An upper bound for the energy of an explicit configuration (`Init` and kernel modules only)

A point of the unit sphere with rational coordinates is stored as four numbers `a, b, c, d`: the point is
`((a - d) / d, (b - d) / d, (c - d) / d)` (the shift by `d` makes the numbers natural).

`upperOk N s pts rs tp tq`: the points `0, …, N - 1` of the list are on the unit sphere (`unitOk`); for every pair
`i < j` the number `r / 2 ^ s`, `r = rs j i > 0`, is at most the distance of the two points, and their inner
product is at most `73/100` (`pairOk`); and the sum of the numbers `⌈2 ^ (2 s) / r⌉ / 2 ^ s ≥ 2 ^ s / r` over the
pairs is at most `tp / tq`. The check is bit-exact with `cert/upper.py`; its use is `N11.Circ.upper_sound`
(`Upper.lean`).
-/

@[expose] public section

namespace N11.Circ

open CAP CAP.Wsos

/-- A point with rational coordinates: `((a - d) / d, (b - d) / d, (c - d) / d)`. -/
structure Pt where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

noncomputable def nthPt : List Pt → Nat → Pt :=
  List.rec (motive := fun _ => Nat → Pt) (fun _ => ⟨0, 0, 0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Pt) h (fun j _ => ih j) i)

/-- The point is on the unit sphere: `a² + b² + c² + 2 d² = 2 d (a + b + c)` and `d > 0`. -/
noncomputable def unitOk (p : Pt) : Bool :=
  Nat.blt 0 p.d
    && Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul p.a p.a) (Nat.mul p.b p.b)) (Nat.mul p.c p.c)) (Nat.mul 2 (Nat.mul p.d p.d)))
      (Nat.mul (Nat.mul 2 p.d) (Nat.add (Nat.add p.a p.b) p.c))

/-- `wPos p q - wNeg p q = d_p d_q (1 - ⟨p, q⟩)`. -/
noncomputable def wPos (p q : Pt) : Nat :=
  Nat.add (Nat.mul q.d (Nat.add (Nat.add p.a p.b) p.c)) (Nat.mul p.d (Nat.add (Nat.add q.a q.b) q.c))

noncomputable def wNeg (p q : Pt) : Nat :=
  Nat.add (Nat.mul 2 (Nat.mul p.d q.d)) (Nat.add (Nat.add (Nat.mul p.a q.a) (Nat.mul p.b q.b)) (Nat.mul p.c q.c))

/-- `r / 2 ^ s` is positive and at most the distance of the points, and their inner product is at most `73/100`:
`r² d_p d_q ≤ 2 ^ (2 s + 1) (wPos - wNeg)` and `27 d_p d_q ≤ 100 (wPos - wNeg)`. -/
noncomputable def pairOk (s : Nat) (p q : Pt) (r : Nat) : Bool :=
  Nat.blt 0 r
    && Nat.ble (Nat.add (Nat.mul (Nat.mul r r) (Nat.mul p.d q.d)) (Nat.mul (Nat.pow 2 (Nat.succ (Nat.mul 2 s))) (wNeg p q)))
      (Nat.mul (Nat.pow 2 (Nat.succ (Nat.mul 2 s))) (wPos p q))
    && Nat.ble (Nat.add (Nat.mul 27 (Nat.mul p.d q.d)) (Nat.mul 100 (wNeg p q))) (Nat.mul 100 (wPos p q))

/-- `⌈2 ^ (2 s) / r⌉`. -/
noncomputable def invUp (s r : Nat) : Nat := Nat.div (Nat.add (Nat.pow 2 (Nat.mul 2 s)) (Nat.pred r)) r

/-- The entry of the pair `i < j` in a table in rows. -/
noncomputable def rAt (rs : List (List Nat)) (i j : Nat) : Nat := nth (nthL rs j) i

/-- The configuration of the points `0, …, N - 1` is on the unit sphere, its inner products are at most `73/100`,
and its Coulomb energy is at most `tp / tq`. -/
noncomputable def upperOk (N s : Nat) (pts : List Pt) (rs : List (List Nat)) (tp tq : Nat) : Bool :=
  Nat.blt 0 tq && allN (fun i => unitOk (nthPt pts i)) N
    && allN (fun j => allN (fun i => pairOk s (nthPt pts i) (nthPt pts j) (rAt rs i j)) j) N
    && Nat.ble (Nat.mul (sumN (fun i => sumN (fun j => cond (Nat.blt i j) (invUp s (rAt rs i j)) 0) N) N) tq)
      (Nat.mul tp (Nat.pow 2 s))

end N11.Circ
