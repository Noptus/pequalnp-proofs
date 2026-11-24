import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

theorem PEqualNP.Outside.L_meta_1630 :
    ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    (∀ x y : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) → (∀ v : Fin N, x v = true → y v = true) → (y p0 = true ∨ y p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → y u = true)) ∧
    (∀ t : Fin N, ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true)) ∧
    (∀ t : Fin N, ∀ p ∈ L t, (T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) := by
  classical
  intro q N L i0 p0 p1 _hq _hN _hsize hint _hjoin hp01 hp0i hp1i T hT
  have hline : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t ht0 ht1
    by_contra hne
    have hc : (L t ∩ L i0).card ≤ 1 := (hint t i0 hne).le
    exact hp01 (Finset.card_le_one.mp hc p0 (Finset.mem_inter.mpr ⟨ht0, hp0i⟩)
      p1 (Finset.mem_inter.mpr ⟨ht1, hp1i⟩))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with hx0 | hx1 | hxoff
    · exact Or.inl (hxy p0 hx0)
    · exact Or.inr (Or.inl (hxy p1 hx1))
    · exact Or.inr (Or.inr (fun u hu => hxy u (hxoff u hu)))
  · intro t
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · right
        right
        intro u hu
        exact decide_eq_true (by simpa only [hline t ht0 ht1] using hu)
      · exact Or.inr (Or.inl (decide_eq_true ht1))
    · exact Or.inl (decide_eq_true ht0)
  · intro t p _hp
    by_cases hp0 : p = p0
    · exact Or.inl ((hT t p p0).mpr (Or.inl hp0.symm))
    by_cases hp1 : p = p1
    · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl hp1.symm)))
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · right
        right
        intro u hu
        apply (hT t p u).mpr
        exact Or.inr (Or.inr (Or.inr ⟨ht0, ht1, hp0, hp1,
          by simpa only [hline t ht0 ht1] using hu⟩))
      · exact Or.inr (Or.inl ((hT t p p1).mpr
          (Or.inr (Or.inr (Or.inl ⟨ht0, ht1, hp0, rfl⟩)))))
    · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨ht0, hp1, rfl⟩)))
  · intro t
    constructor
    · apply decide_eq_false
      rintro ⟨v, hv, hnot⟩
      exact (of_decide_eq_true hnot) hv
    · intro p hp
      exact decide_eq_true ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
