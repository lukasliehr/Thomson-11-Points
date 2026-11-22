module

public import N11.ParallelResearch1.Circ.Kernel
public import N11.ParallelResearch1.Circ.GraphKernel

/-!
# Cells of eleven labelled points: the checks of a cover and of a penalty (`Init` and kernel modules only)

A *cell* is a table of intervals for the pairs `a < b < N` of labelled points (`Nat → Nat → Ival`).

* `onesOk N q C Dm`: the certificate has the classes `0, …, N - 1` with one point each and empty classes from `N`
  on, and its domain has no further inequalities; so its domain is the cell `Dm.iv`.
* `ivsBeq N f g`: two cells have the same intervals (the same six numbers for every pair). `ivsSub N f g`: every
  interval of `f` is contained in that of `g` (`subIv`; comparisons of fractions with positive denominators, `qle`).
* `patCell g`: the cell of the pattern `g`: `[-2/25, 73/100]` on its edges and `[-1, -2/25]` on the other pairs.
* `slabIv c b T u v side`: a slab of the peel of the cell `c` around the box `b`, for the pair `(u, v)`: the pairs whose
  position in the order `T` (`posAt`, six bits each) is before that of `(u, v)` have their intervals of the box, the
  pair `(u, v)` has the part of its interval of `c` below the box (`side = 0`) or above it (`side = 1`), and the other
  pairs have their intervals of `c`. `sideEmpty`: the box reaches that end of the interval of `c`.
* `halfOk N s da db u v`: the cells `da`, `db` are the two halves of the cell `s` along the pair `(u, v)`.
  `halfSub N s da db u v`: the cell `s` is covered by `da` and `db`, which contain `s` in all pairs but `(u, v)` and
  whose intervals of `(u, v)` cover that of `s`.
* `penIs cn cd tb tp tn sP S`: the polynomial `pen` of the witness `S` is `(cn / cd) (t - (tp - tn) / 2 ^ tb)²`;
  `pensAre`: this holds for all pairs, with the numbers `tp`, `tn` of a table with 26 bits for every pair (`tauP`,
  `tauN`: bit 0 is the sign).

The checks are bit-exact with `cert/cellref.py`; their use is in `Cell.lean`.
-/

@[expose] public section

namespace N11.Circ

open CAP CAP.Wsos

/-- The certificate has `N` classes of one point and no others; its domain has no further inequalities. -/
noncomputable def onesOk (N q : Nat) (C : Cert) (Dm : Dom) : Bool :=
  Nat.blt N q && allN (fun a => Nat.beq (C.n a) 1) N && allN (fun c => Nat.blt c N || Nat.beq (C.n c) 0) q
    && List.isEmpty Dm.cuts

/-- The left end points of two intervals are the same numbers. -/
noncomputable def loBeq (I J : Ival) : Bool := Nat.beq I.lp J.lp && Nat.beq I.ln J.ln && Nat.beq I.ld J.ld

/-- The right end points of two intervals are the same numbers. -/
noncomputable def hiBeq (I J : Ival) : Bool := Nat.beq I.hp J.hp && Nat.beq I.hn J.hn && Nat.beq I.hd J.hd

/-- The left end point of `I` is the right end point of `J`. -/
noncomputable def loHiBeq (I J : Ival) : Bool := Nat.beq I.lp J.hp && Nat.beq I.ln J.hn && Nat.beq I.ld J.hd

/-- Two cells have the same intervals. -/
noncomputable def ivsBeq (N : Nat) (f g : Nat → Nat → Ival) : Bool :=
  allN (fun b => allN (fun a => ivalBeq (f a b) (g a b)) b) N

/-- The cell of a pattern. -/
noncomputable def patCell (g : Nat) : Nat → Nat → Ival :=
  fun a b => cond (tbit g (Nat.add (pairs b) a)) ivEdge ivFar

/-- The position of the pair `a < b` in the order of a peel: six bits each. -/
noncomputable def posAt (T a b : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 6 (Nat.add (pairs b) a))) 63

/-- The part of the interval `I` below the interval `J`. -/
noncomputable def below (I J : Ival) : Ival := ⟨I.lp, I.ln, I.ld, J.lp, J.ln, J.ld⟩

/-- The part of the interval `I` above the interval `J`. -/
noncomputable def above (I J : Ival) : Ival := ⟨J.hp, J.hn, J.hd, I.hp, I.hn, I.hd⟩

/-- A slab of the peel of the cell `c` around the box `b`. -/
noncomputable def slabIv (c b : Nat → Nat → Ival) (T u v side : Nat) : Nat → Nat → Ival :=
  fun a b' => cond (Nat.blt (posAt T a b') (posAt T u v)) (b a b')
    (cond (Nat.beq a u && Nat.beq b' v) (cond (Nat.beq side 0) (below (c u v) (b u v)) (above (c u v) (b u v)))
      (c a b'))

/-- The box reaches the end of the interval of the cell: there is no slab on this side. -/
noncomputable def sideEmpty (c b : Nat → Nat → Ival) (u v side : Nat) : Bool :=
  cond (Nat.beq side 0) (loBeq (c u v) (b u v)) (hiBeq (c u v) (b u v))

/-- The cells `da` and `db` are the halves of the cell `s` along the pair `(u, v)`. -/
noncomputable def halfOk (N : Nat) (s da db : Nat → Nat → Ival) (u v : Nat) : Bool :=
  allN (fun b' => allN (fun a => cond (Nat.beq a u && Nat.beq b' v)
      (loBeq (da a b') (s a b') && hiBeq (db a b') (s a b') && loHiBeq (db a b') (da a b'))
      (ivalBeq (da a b') (s a b') && ivalBeq (db a b') (s a b'))) b') N

/-- `(p1 - n1) / d1 ≤ (p2 - n2) / d2` for positive denominators. -/
noncomputable def qle (p1 n1 d1 p2 n2 d2 : Nat) : Bool :=
  Nat.ble (Nat.add (Nat.mul p1 d2) (Nat.mul n2 d1)) (Nat.add (Nat.mul p2 d1) (Nat.mul n1 d2))

/-- The denominators of the interval are positive. -/
noncomputable def posDen (I : Ival) : Bool := Nat.blt 0 I.ld && Nat.blt 0 I.hd

/-- The interval `I` is contained in the interval `J`. -/
noncomputable def subIv (I J : Ival) : Bool :=
  posDen I && posDen J && qle J.lp J.ln J.ld I.lp I.ln I.ld && qle I.hp I.hn I.hd J.hp J.hn J.hd

/-- Every interval of the cell `f` is contained in that of the cell `g`. -/
noncomputable def ivsSub (N : Nat) (f g : Nat → Nat → Ival) : Bool :=
  allN (fun b => allN (fun a => subIv (f a b) (g a b)) b) N

/-- The box reaches the end of the interval of the cell or goes beyond it: there is no slab on this side. -/
noncomputable def sideOut (c b : Nat → Nat → Ival) (u v side : Nat) : Bool :=
  posDen (c u v) && posDen (b u v)
    && cond (Nat.beq side 0) (qle (b u v).lp (b u v).ln (b u v).ld (c u v).lp (c u v).ln (c u v).ld)
        (qle (c u v).hp (c u v).hn (c u v).hd (b u v).hp (b u v).hn (b u v).hd)

/-- The cell `s` is covered by the cells `da` and `db`: they contain `s` in all pairs but `(u, v)`; there `da`
begins at or before `s`, `db` ends at or after `s`, and `db` begins at or before the end of `da`. -/
noncomputable def halfSub (N : Nat) (s da db : Nat → Nat → Ival) (u v : Nat) : Bool :=
  allN (fun b' => allN (fun a => cond (Nat.beq a u && Nat.beq b' v)
      (posDen (s a b') && posDen (da a b') && posDen (db a b')
        && qle (da a b').lp (da a b').ln (da a b').ld (s a b').lp (s a b').ln (s a b').ld
        && qle (s a b').hp (s a b').hn (s a b').hd (db a b').hp (db a b').hn (db a b').hd
        && qle (db a b').lp (db a b').ln (db a b').ld (da a b').hp (da a b').hn (da a b').hd)
      (subIv (s a b') (da a b') && subIv (s a b') (db a b'))) b') N

/-- The polynomial `pen` of the witness is `(cn / cd) (t - (tp - tn) / 2 ^ tb)²`: with `Dn = 2 ^ sP * sc`,
`a2 cd = cn Dn`, `a1 cd 2 ^ tb = -2 cn (tp - tn) Dn`, `a0 cd 4 ^ tb = cn (tp - tn)² Dn`, and `tp = 0` or `tn = 0`. -/
noncomputable def penIs (cn cd tb tp tn sP : Nat) (S : Sign2) : Bool :=
  Nat.blt 0 cd && Nat.blt 0 S.sc && (Nat.beq tp 0 || Nat.beq tn 0)
    && Nat.beq S.pen.a2n 0 && Nat.beq (Nat.mul S.pen.a2p cd) (Nat.mul cn (Nat.mul (Nat.pow 2 sP) S.sc))
    && Nat.beq (Nat.add (Nat.mul (Nat.mul S.pen.a1p cd) (Nat.pow 2 tb)) (Nat.mul (Nat.mul (Nat.mul 2 cn) tp) (Nat.mul (Nat.pow 2 sP) S.sc)))
        (Nat.add (Nat.mul (Nat.mul S.pen.a1n cd) (Nat.pow 2 tb)) (Nat.mul (Nat.mul (Nat.mul 2 cn) tn) (Nat.mul (Nat.pow 2 sP) S.sc)))
    && Nat.beq S.pen.a0n 0
    && Nat.beq (Nat.mul (Nat.mul S.pen.a0p cd) (Nat.pow 4 tb))
        (Nat.mul (Nat.mul cn (Nat.add (Nat.mul tp tp) (Nat.mul tn tn))) (Nat.mul (Nat.pow 2 sP) S.sc))

/-- The entry of the pair `a < b` in a table of centres: 26 bits each, bit 0 the sign. -/
noncomputable def tauE (T a b : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 26 (Nat.add (pairs b) a))) 67108863

noncomputable def tauP (T a b : Nat) : Nat := cond (Nat.beq (Nat.land (tauE T a b) 1) 0) (Nat.shiftRight (tauE T a b) 1) 0

noncomputable def tauN (T a b : Nat) : Nat := cond (Nat.beq (Nat.land (tauE T a b) 1) 0) 0 (Nat.shiftRight (tauE T a b) 1)

/-- The polynomials `pen` of all pairs `a < b < N` are `(cn / cd) (t - τ)²` with the centres `τ` of the table. -/
noncomputable def pensAre (N cn cd tb T sP : Nat) (l : List (List Sign2)) : Bool :=
  allN (fun b => allN (fun a => penIs cn cd tb (tauP T a b) (tauN T a b) sP (signOfRows l a b)) b) N

end N11.Circ
