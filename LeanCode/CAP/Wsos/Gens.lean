module

public import CAP.Wsos.Shares

/-!
# The numbers of the checker stand for the polynomials of the data: generators and weights

`gensGo_rep`, `gensV_bd`: the product of the generators of a weight.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

theorem powM_eq (mM w : ℕ) : ∀ e, powM mM w e = pwr mM w 1 e
  | 0 => rfl
  | e + 1 => by
    show mulM mM (powM mM w e) w = mulM mM (pwr mM w 1 e) w
    rw [powM_eq mM w e]

theorem genGo_cons (u v t deg : ℕ) (tm : Term) (terms : List Term) (Pp Nn : ℕ) :
    genGo P pM mM u v t deg (tm :: terms) Pp Nn
      = genGo P pM mM u v t deg terms
          (Nat.add Pp (Nat.mul tm.cp (Nat.shiftLeft (mulM mM (mulM mM (powM mM u tm.e1) (powM mM v tm.e2)) (powM mM t tm.e3))
            (Nat.mul P.m (Nat.sub deg (Nat.add (Nat.add tm.e1 tm.e2) tm.e3))))))
          (Nat.add Nn (Nat.mul tm.cn (Nat.shiftLeft (mulM mM (mulM mM (powM mM u tm.e1) (powM mM v tm.e2)) (powM mM t tm.e3))
            (Nat.mul P.m (Nat.sub deg (Nat.add (Nat.add tm.e1 tm.e2) tm.e3)))))) := rfl

theorem mon_rep (hM : Mod P pM mM) {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T)
    (deg : ℕ) (tm : Term) :
    Rep P (Nat.shiftLeft (mulM mM (mulM mM (powM mM u tm.e1) (powM mM v tm.e2)) (powM mM t tm.e3))
        (Nat.mul P.m (Nat.sub deg (Nat.add (Nat.add tm.e1 tm.e2) tm.e3))))
      ((EP P) ^ (deg - (tm.e1 + tm.e2 + tm.e3)) * (U ^ tm.e1 * V ^ tm.e2 * T ^ tm.e3)) := by
  rw [powM_eq, powM_eq, powM_eq]
  have h := (((pwr_rep hM hu tm.e1).mulM hM (pwr_rep hM hv tm.e2)).mulM hM (pwr_rep hM ht tm.e3)).shiftLeft
    (P.m * (deg - (tm.e1 + tm.e2 + tm.e3)))
  refine h.congr ?_
  rw [C_two_pow, pow_mul]

theorem genGo_rep (hM : Mod P pM mM) {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T)
    (deg : ℕ) : ∀ (terms : List Term) (Pp Nn : ℕ) (PF NF : Poly), Rep P Pp PF → Rep P Nn NF →
      Rep P (genGo P pM mM u v t deg terms Pp Nn) (PF - NF + (terms.map (termV (EP P) U V T deg)).sum)
  | [], Pp, Nn, PF, NF, hp, hn => by
    simpa [genGo] using (hp.subM hM hn).land hM
  | tm :: terms, Pp, Nn, PF, NF, hp, hn => by
    rw [genGo_cons]
    have hmon := mon_rep hM hu hv ht deg tm
    have ih := genGo_rep hM hu hv ht deg terms _ _ _ _ (hp.add (Rep.smul tm.cp hmon)) (hn.add (Rep.smul tm.cn hmon))
    refine ih.congr ?_
    rw [List.map_cons, List.sum_cons]
    unfold termV
    rw [C_natCast', C_natCast']
    ring

theorem gen_rep (hM : Mod P pM mM) {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T)
    (g : Gen) : Rep P (genGo P pM mM u v t g.deg g.terms 0 0) (genV (EP P) U V T g) := by
  have := genGo_rep hM hu hv ht g.deg g.terms 0 0 0 0 Rep.zero Rep.zero
  refine this.congr ?_
  unfold genV
  ring

theorem gensGo_cons (u v t : ℕ) (g : Gen) (gens : List Gen) (acc : ℕ) :
    gensGo P pM mM u v t (g :: gens) acc
      = gensGo P pM mM u v t gens (mulM mM acc (genGo P pM mM u v t g.deg g.terms 0 0)) := rfl

theorem gensGo_rep (hM : Mod P pM mM) {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T) :
    ∀ (gens : List Gen) (acc : ℕ) (AF : Poly), Rep P acc AF →
      Rep P (gensGo P pM mM u v t gens acc) (AF * gensV (EP P) U V T gens)
  | [], acc, AF, ha => by simpa [gensGo, gensV] using ha
  | g :: gens, acc, AF, ha => by
    rw [gensGo_cons]
    have ih := gensGo_rep hM hu hv ht gens _ _ (ha.mulM hM (gen_rep hM hu hv ht g))
    refine ih.congr ?_
    unfold gensV
    rw [List.map_cons, List.prod_cons]
    ring

/-! ## Bounds -/

theorem termsOk_cons (deg : ℕ) (tm : Term) (terms : List Term) :
    termsOk deg (tm :: terms) = (Nat.ble (Nat.add (Nat.add tm.e1 tm.e2) tm.e3) deg && termsOk deg terms) := rfl

theorem termSum_cons (tm : Term) (terms : List Term) : termSum (tm :: terms) = tm.cp + tm.cn + termSum terms := rfl

theorem termV_bd {U V T : Poly} (hu : Bd U (2 ^ P.m) 1) (hv : Bd V (2 ^ P.m) 1) (ht : Bd T (2 ^ P.m) 1) (deg : ℕ)
    (tm : Term) (hdeg : tm.e1 + tm.e2 + tm.e3 ≤ deg) :
    Bd (termV (EP P) U V T deg tm) ((tm.cp + tm.cn) * (2 ^ P.m) ^ deg) deg := by
  unfold termV
  have hc : Bd (((tm.cp : ℕ) : Poly) - ((tm.cn : ℕ) : Poly)) (tm.cp + tm.cn) 0 := by
    have := (Bd.natCast tm.cp).sub (Bd.natCast tm.cn)
    rwa [C_natCast', C_natCast'] at this
  have he : Bd ((EP P) ^ (deg - (tm.e1 + tm.e2 + tm.e3))) ((2 ^ P.m) ^ (deg - (tm.e1 + tm.e2 + tm.e3))) 0 := by
    have := (bd_two_pow P.m).pow (deg - (tm.e1 + tm.e2 + tm.e3))
    simpa using this
  have hm := ((hu.pow tm.e1).mul (hv.pow tm.e2)).mul (ht.pow tm.e3)
  refine (hc.mul (he.mul hm)).mono (le_of_eq ?_) (by omega)
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 2
  omega

theorem genV_bd {U V T : Poly} (hu : Bd U (2 ^ P.m) 1) (hv : Bd V (2 ^ P.m) 1) (ht : Bd T (2 ^ P.m) 1) (deg : ℕ) :
    ∀ (terms : List Term), termsOk deg terms = true →
      Bd ((terms.map (termV (EP P) U V T deg)).sum) (termSum terms * (2 ^ P.m) ^ deg) deg
  | [], _ => by simpa [termSum] using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le deg)
  | tm :: terms, h => by
    rw [termsOk_cons, Bool.and_eq_true, Nat.ble_eq] at h
    rw [List.map_cons, List.sum_cons, termSum_cons, add_mul]
    exact (termV_bd hu hv ht deg tm h.1).add (genV_bd hu hv ht deg terms h.2)

theorem nGen_eq (P : Params) (g : Gen) : nGen P g = termSum g.terms * (2 ^ P.m) ^ g.deg := by
  show (termSum g.terms) <<< (P.m * g.deg) = _
  rw [Nat.shiftLeft_eq, pow_mul]

theorem gensOk_cons (g : Gen) (gens : List Gen) : gensOk (g :: gens) = (termsOk g.deg g.terms && gensOk gens) := rfl

theorem degSum_cons (g : Gen) (gens : List Gen) : degSum (g :: gens) = g.deg + degSum gens := rfl

theorem nGens_cons (g : Gen) (gens : List Gen) : nGens P (g :: gens) = nGen P g * nGens P gens := rfl

theorem gensV_bd {U V T : Poly} (hu : Bd U (2 ^ P.m) 1) (hv : Bd V (2 ^ P.m) 1) (ht : Bd T (2 ^ P.m) 1) :
    ∀ (gens : List Gen), gensOk gens = true → Bd (gensV (EP P) U V T gens) (nGens P gens) (degSum gens)
  | [], _ => by simpa [gensV, nGens, degSum] using Bd.one
  | g :: gens, h => by
    rw [gensOk_cons, Bool.and_eq_true] at h
    unfold gensV
    rw [List.map_cons, List.prod_cons, nGens_cons, degSum_cons, nGen_eq]
    exact (genV_bd hu hv ht g.deg g.terms h.1).mul (gensV_bd hu hv ht gens h.2)

end CAP.Wsos
