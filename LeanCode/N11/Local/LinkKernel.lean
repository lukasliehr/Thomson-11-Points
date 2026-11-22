module

public import N11.Local.Kernel
public import N11.ParallelResearch1.Circ.CellKernel

/-!
# G7 of route G: the reference configuration and the centres of the inner box (`Init` and kernel modules only)

The inner certificates of the route (statement G6) confine the inner products of a minimizer to the centres
`tau_ab` of a table `T` (`N11.Circ.tauP`, `N11.Circ.tauN`: 26 bits for a pair, bit 0 the sign, `tb` binary places).
`linkOk D T tb del`: the inner products of the reference configuration of G7 are close to these centres,
`∑_{a<b} (2^tb <P_a, P_b> - 2^120 (tauP - tauN))² ≤ del`. The check is bit-exact with `link_sum` of
`N11/g7/gen.py`. Soundness: `N11/Local/Link.lean`.
-/

@[expose] public section

namespace N11.Local

/-- `2^tb <P_a, P_b> - 2^120 (tauP - tauN)`, scale `2^(120 + tb)`. -/
noncomputable def linkD (D : Dat) (T tb a b : Nat) : Nat × Nat :=
  zsub (znat (Nat.shiftLeft 1 tb) (tI D a b))
    (znat (Nat.shiftLeft 1 120) (N11.Circ.tauP T a b, N11.Circ.tauN T a b))

/-- The sum of the squares of `linkD` over the pairs `a < b < 11` is at most `del`. -/
noncomputable def linkOk (D : Dat) (T tb del : Nat) : Bool :=
  zle (zsumP fun a b => Prod.rec (motive := fun _ => Nat × Nat) (fun d1 d2 => zmul (d1, d2) (d1, d2))
    (linkD D T tb a b)) (del, 0)

end N11.Local
