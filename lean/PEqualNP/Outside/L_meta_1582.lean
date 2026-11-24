import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

theorem PEqualNP.Outside.L_meta_1582 :
    ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  classical
  intro q m N L i0 T0 _ hm _ _ _ hinter _ hT hTm
  have hmono : ∀ x y : Fin N → Bool,
      ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      (∀ v : Fin N, x v = true → y v = true) →
      ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true) := by
    intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hx
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hx v hv))
  have hbound : ∀ t : Fin N, t ≠ i0 →
      m - 1 ≤ (T0.filter (fun v => v ∉ L t)).card := by
    intro t ht
    have hsub : T0.filter (fun v => v ∈ L t) ⊆ L t ∩ L i0 := by
      intro v hv
      obtain ⟨hvT, hvt⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_inter.mpr ⟨hvt, hT hvT⟩
    have hone := Finset.card_le_card hsub
    rw [hinter t i0 ht] at hone
    have hsum := Finset.card_filter_add_card_filter_not (s := T0) (fun v => v ∈ L t)
    rw [hTm] at hsum
    omega
  have hcol : ∀ t : Fin N,
      ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true) := by
    intro t
    by_cases ht : t = i0
    · subst t
      right
      intro v hv
      simpa using hv
    · have hpos : 0 < (T0.filter (fun v => v ∉ L t)).card := by
        have hb := hbound t ht
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      obtain ⟨hvT, hvt⟩ := Finset.mem_filter.mp hv
      exact Or.inl ⟨v, hvT, by simpa using hvt⟩
  refine ⟨hmono, hcol, hbound, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · exact hcol i0
  · intro r _
    right
    intro v hv
    simp [hv]
  · intro t
    constructor
    · simp
    · intro p hp
      constructor
      · apply hmono _ _ (hcol t)
        intro v hv
        have hvt : v ∉ L t := by simpa using hv
        simp [hvt]
      · simp only [decide_eq_true_eq]
        exact ⟨p, hp, Or.inr rfl⟩
