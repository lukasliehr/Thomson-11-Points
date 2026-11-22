module

public import CAP.Wsos.CertKernel

/-!
# Patterns of contact graphs (`Init` and kernel modules only)

A *pattern* on `k` vertices is a natural number `g`: the bit `pairs b + a` of `g`, `pairs b = b (b - 1) / 2`, belongs
to the pair `a < b` of vertices (`adjG`). Adding a vertex `k` with the set `S` of neighbours adds `S * 2 ^ pairs k`.

`patOk N k g q C Dm`: the certificate `C` with `q` classes and the domain `Dm` has the classes `0, …, k - 1` with one
point each and the class `k` with the `N - k` further points; the classes above `k` are empty (the last one is the
class of the root); the interval of the pair type `(a, b)`, `a < b < k`, is `[-2/25, 73/100]` if the pair is an edge
of `g` and `[-1, -2/25]` otherwise; the intervals of the pair types with the class `k` are `[-1, 73/100]`; the domain
has no further inequalities. The check is bit-exact with `cert/ref.py`; its use is `N11.Circ.excl_of_rows`
(`Graph.lean`).
-/

@[expose] public section

namespace N11.Circ

open CAP CAP.Wsos

/-- The bit `i` of `g`. -/
def tbit (g i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight g i) 1) 1

/-- The number of pairs of `b` vertices. -/
def pairs (b : Nat) : Nat := Nat.div (Nat.mul b (Nat.pred b)) 2

/-- The vertices `u ≠ v` are adjacent in the pattern `g`. -/
def adjG (g u v : Nat) : Bool :=
  cond (Nat.blt u v) (tbit g (Nat.add (pairs v) u)) (tbit g (Nat.add (pairs u) v))

def ivalBeq (I J : Ival) : Bool :=
  Nat.beq I.lp J.lp && Nat.beq I.ln J.ln && Nat.beq I.ld J.ld && Nat.beq I.hp J.hp && Nat.beq I.hn J.hn && Nat.beq I.hd J.hd

/-- The interval `[-2/25, 73/100]` of an edge. -/
def ivEdge : Ival := ⟨0, 2, 25, 73, 0, 100⟩

/-- The interval `[-1, -2/25]` of a pair that is not an edge. -/
def ivFar : Ival := ⟨0, 1, 1, 0, 2, 25⟩

/-- The interval `[-1, 73/100]` of a pair with a further point. -/
def ivFree : Ival := ⟨0, 1, 1, 73, 0, 100⟩

/-- The certificate has the domain of the pattern `g` on `k` labelled points among `N` points. -/
noncomputable def patOk (N k g q : Nat) (C : Cert) (Dm : Dom) : Bool :=
  Nat.blt k q && Nat.beq (Nat.add (C.n k) k) N
    && allN (fun c => Nat.ble c k || Nat.beq (C.n c) 0) q
    && allN (fun a => Nat.beq (C.n a) 1) k
    && allN (fun b => allN (fun a => ivalBeq (Dm.iv a b) (cond (tbit g (Nat.add (pairs b) a)) ivEdge ivFar)) b) k
    && allN (fun a => Nat.beq (C.n k) 0 || ivalBeq (Dm.iv a k) ivFree) k
    && (Nat.ble (C.n k) 1 || ivalBeq (Dm.iv k k) ivFree)
    && List.isEmpty Dm.cuts

end N11.Circ
