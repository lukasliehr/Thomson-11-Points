module

public import CAP.Wsos.Layout

/-!
# The layout of degree 6

The map `x ^ a * y ^ b * z ^ c ↦ a + 22 * b + 28 * c` is injective on the monomials of total degree at most 6:
the layout that `certgen/s3n9_box.py` chooses for `D = 6` (the pair with the smallest `k2`). The kernel
evaluates the test `CAP.Wsos.layoutOk`.
-/

@[expose] public section

namespace N11.Circ

open CAP.Wsos

set_option maxRecDepth 1000000 in
theorem layoutInj_6 : LayoutInj 6 22 28 := layoutInj_of_ok (by decide +kernel)

end N11.Circ
