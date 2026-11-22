module

public import N11.Local.Cubic
public import N11.Local.Small

/-!
# G7 of route G for eleven points: the statement from the checks of the kernel

`g7_of`: if the kernel accepts the nine checks of `N11/Local/Kernel.lean` for the data `D` (for the cubic form: the
33 blocks of the table and the 561 entries of the Gram matrix), then the statement `G7` of `N11/Local/Forms.lean`
holds for the reference configuration `rp D`, the coefficients `ra D`, `rb D`, `rc D` and the constants of the
checks. The constants `kappa = nk / dk`, `sigma² = ns / ds` and `c3 = nc / dc` enter the checks as integers at the
scales `2^181`, `2^120` and `36 * 2^1200`.
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

/-- **The statement G7 from the checks of the kernel.** -/
theorem g7_of (D : Dat) (E Gam Ra Rb Rc ne tmax kap K sig KR off c3s : ℕ) (tab : List (List (List ℕ)))
    (PQ : PSD.Params) (rowsQ colsQ : ℕ) (PR : PSD.Params) (rowsR colsR : ℕ) (PC : PSD.Params) (rowsC colsC : ℕ)
    (nk dk Kp ns ds nc dc : ℕ)
    (henc : encOk D E = true) (hsym : symOk D = true) (hgrad : gradOk D Gam = true)
    (hrows : rowsOk D Ra Rb Rc = true) (hnorm : normOk D ne = true) (htop : topOk D tmax = true)
    (hhess : hessOk D kap K PQ rowsQ colsQ = true) (hrig : rigOk D sig KR PR rowsR colsR = true)
    (htab : ∀ a, a < 33 → tabOk D off (getLLN tab a) a = true) (hcub : cubOk tab PC rowsC colsC = true)
    (hw : ∀ k s, k < 33 → s < 33 - k → wEntOk off c3s tab PC rowsC k s = true)
    (hk : kap * dk = nk * 2 ^ 181) (hdk : 0 < dk) (hK : K = Kp * 2 ^ 61)
    (hs : sig * ds = ns * 2 ^ 120) (hds : 0 < ds)
    (hc : c3s * dc ^ 2 = 36 * nc ^ 2 * 2 ^ 1200) (hdc : 0 < dc) :
    G7 (rp D) (ra D) (rb D) (rc D)
      { eps := (E : ℝ) / 2 ^ 60, gam := (Gam : ℝ) / 2 ^ 240, ra := (Ra : ℝ) / 2 ^ 60, rb := (Rb : ℝ) / 2 ^ 60,
        rc := (Rc : ℝ) / 2 ^ 60, nu := (ne : ℝ) / 2 ^ 120, tmax := (tmax : ℝ) / 2 ^ 120,
        kappa := (nk : ℝ) / (dk : ℝ), penQ := (Kp : ℝ), sigma2 := (ns : ℝ) / (ds : ℝ), penR := (KR : ℝ),
        c3 := (nc : ℝ) / (dc : ℝ) } where
  norm := norm D ne hnorm
  top := top D tmax htop
  sym := sym D hsym
  enc := enc D E henc
  grad := grad D Gam hgrad
  rows := rows D Ra Rb Rc hrows
  hess := hess D kap K PQ rowsQ colsQ hhess nk dk Kp hk hdk hK
  rig := rig D sig KR PR rowsR colsR hrig ns ds hs hds
  cub := cub D off c3s tab PC rowsC colsC htab hcub hw nc dc hdc hc

end N11.Local
