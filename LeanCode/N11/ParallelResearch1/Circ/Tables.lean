module

public import N11.ParallelResearch1.Circ.Energy

/-!
# The conditions on the tables of a certificate

`tablesOk_sound`: if `N11.Circ.tablesOk P C xs = true` and `Q + 1 = q`, then the index class `Q` of the root is
empty, every class below `Q` has `d + 1` Gram matrices, the class of the share equation of every pair type is
its largest class with further points, and the list `xs` contains every triple type that occurs.

`certHolds2_of`: the hypotheses `CertHolds2` of the typed bound from this check, from the statements of the Gram
matrices (`CAP.Wsos.gramOk_holds`) and from the statements of the triple types (`checkTy2_holds`).
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

theorem tablesOk_sound {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (hQ : Q + 1 = P.q) (h : tablesOk P C xs = true) :
    C.n Q = 0 ∧ (∀ a < Q, (C.gram a).length = P.d + 1)
      ∧ (∀ a < P.q, ∀ b < P.q, a ≤ b →
          C.last a b < P.q ∧ 0 < mult C a b (C.last a b) ∧ ∀ x < P.q, C.last a b < x → mult C a b x = 0)
      ∧ (∀ a < P.q, ∀ b < P.q, ∀ c < P.q, a ≤ b → b ≤ c → 0 < mult C b c a → 0 < mult C a c b →
          0 < mult C a b c → hasX a b c xs = true) := by
  have e : Nat.pred P.q = Q := by
    rw [← hQ]
    rfl
  unfold tablesOk at h
  rw [e] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, hn⟩, hlen⟩, hlast⟩, hcov⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true hn, ?_, ?_, ?_⟩
  · intro a ha
    have h1 := (allN_iff _ _).mp hlen a ha
    have h2 := Nat.eq_of_beq_eq_true h1
    rw [len_eq] at h2
    exact h2
  · intro a ha b hb hab
    have h1 := (all2N_iff _ _).mp hlast a ha b hb
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · rw [Nat.blt_eq] at h1
      omega
    · rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h1
      refine ⟨h1.1.1, h1.1.2, fun x hx hlx => ?_⟩
      have h2 := (allN_iff _ _).mp h1.2 x hx
      rw [Bool.or_eq_true, Nat.ble_eq] at h2
      rcases h2 with h2 | h2
      · omega
      · exact Nat.eq_of_beq_eq_true h2
  · intro a ha b hb c hc hab hbc m1 m2 m3
    have h1 := (all3N_iff _ _).mp hcov a ha b hb c hc
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at h1
    rcases h1 with ((((h1 | h1) | h1) | h1) | h1) | h1
    · rw [Nat.blt_eq] at h1
      omega
    · rw [Nat.blt_eq] at h1
      omega
    · have := Nat.eq_of_beq_eq_true h1
      omega
    · have := Nat.eq_of_beq_eq_true h1
      omega
    · have := Nat.eq_of_beq_eq_true h1
      omega
    · exact h1

/-- The hypotheses of the typed bound on the data of a certificate. -/
theorem certHolds2_of {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (hQ : Q + 1 = P.q)
    (ht : tablesOk P C xs = true)
    (hgram : ∀ a < Q, ∃ cols : ℕ → List ℕ,
      ∀ k < (C.gram a).length, GramHolds P (P.d - k) (cols k) ((C.gram a).getD k 0))
    (hty : ∀ X ∈ xs, TyHolds2 P (tyOf2 Q C X)) : CertHolds2 P Q C xs := by
  obtain ⟨h1, h2, h3, h4⟩ := tablesOk_sound hQ ht
  exact ⟨hQ, h1, h2, hgram, h3, hty, h4⟩

end N11.Circ
