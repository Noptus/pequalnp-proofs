import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto

theorem PEqualNP.Outside.L_meta_1633 :
    ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  classical
  intro q N L i0 p0 p1 hq _ hcard hmeet _ hp01 hp0 hp1 T hT
  have hnot : ∀ a : Fin N, a ≠ i0 → ¬ (p0 ∈ L a ∧ p1 ∈ L a) := by
    intro a ha hab
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (hmeet a i0 ha)
    have h0 : p0 ∈ L a ∩ L i0 := Finset.mem_inter.mpr ⟨hab.1, hp0⟩
    have h1 : p1 ∈ L a ∩ L i0 := Finset.mem_inter.mpr ⟨hab.2, hp1⟩
    rw [hr, Finset.mem_singleton] at h0 h1
    exact hp01 (h0.trans h1.symm)
  have hdiff : ∀ a b r : Fin N, a ≠ b → ∃ p ∈ L a \ L b, p ≠ r := by
    intro a b r hab
    have hsum := Finset.card_sdiff_add_card_inter (L a) (L b)
    rw [hmeet a b hab, hcard a] at hsum
    have hc : (L a \ L b).card = q := Nat.add_right_cancel hsum
    have hlt : ({r} : Finset (Fin N)).card < (L a \ L b).card := by
      rw [Finset.card_singleton, hc]
      exact lt_of_lt_of_le (by decide : 1 < 3) hq
    obtain ⟨p, hp, hpr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨p, hp, by simpa only [Finset.mem_singleton] using hpr⟩
  have hpoint : ∀ a b : Fin N, a ≠ i0 → a ≠ b →
      ((∃ p ∈ L a \ L b, ∃ v ∈ L b, T a p v = true) ↔
        (p0 ∉ L a ∧ p0 ∈ L b) ∨ (p0 ∈ L a ∧ p1 ∉ L a ∧ p1 ∈ L b)) := by
    intro a b ha hab
    constructor
    · rintro ⟨p, hp, v, hv, htest⟩
      rcases (hT a p v).mp htest with h | h | h | h
      · exact False.elim ((Finset.mem_sdiff.mp hp).2 (h ▸ hv))
      · exact Or.inl ⟨h.1, h.2.2 ▸ hv⟩
      · exact Or.inr ⟨h.1, h.2.1, h.2.2.2 ▸ hv⟩
      · exact False.elim (hnot a ha ⟨h.1, h.2.1⟩)
    · rintro (h | h)
      · obtain ⟨p, hp, hpr⟩ := hdiff a b p1 hab
        refine ⟨p, hp, p0, h.2, (hT a p p0).mpr ?_⟩
        exact Or.inr (Or.inl ⟨h.1, hpr, rfl⟩)
      · obtain ⟨p, hp, hpr⟩ := hdiff a b p0 hab
        refine ⟨p, hp, p1, h.2.2, (hT a p p1).mpr ?_⟩
        exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, hpr, rfl⟩))
  intro t u ht hu htu
  rw [hpoint t u ht htu, hpoint u t hu htu.symm]
  tauto
