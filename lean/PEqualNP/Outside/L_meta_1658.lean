import PEqualNP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

theorem PEqualNP.Outside.L_meta_1658 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
      k0 < gates.length →
      (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
      k0 ∈ Kc →
      (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
      (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
        (∀ bK : Set ℕ, k0 ∈ bK →
          (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
            (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
        gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
        ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
      Bd.card ≤ 2 * Kc.card := by
  classical
  intro n gates S k0 Bd Kc hnorm _htopo _hk0 _hs hk0K hclosed hboundary
  let inputs : ℕ → Finset ℕ := fun k =>
    match gates[k]? with
    | none => ∅
    | some g => g.inputs.toFinset
  have hinputs : ∀ k ∈ Kc, (inputs k).card ≤ 2 := by
    intro k _hk
    dsimp only [inputs]
    cases hget : gates[k]? with
    | none => simp
    | some g =>
      exact (List.toFinset_card_le g.inputs).trans
        (hnorm g (List.mem_of_getElem? hget)).2
  have hsubset : Bd ⊆ Kc.biUnion inputs := by
    intro bw hbw
    obtain ⟨bk, bg, hminimal, hget, _hop, hmem, _hout⟩ := hboundary bw hbw
    have hbk : bk ∈ Kc := hminimal (↑Kc : Set ℕ) hk0K hclosed
    apply Finset.mem_biUnion.mpr
    refine ⟨bk, hbk, ?_⟩
    simpa only [inputs, hget, List.mem_toFinset] using hmem
  calc
    Bd.card ≤ (Kc.biUnion inputs).card := Finset.card_le_card hsubset
    _ ≤ Kc.card * 2 := Finset.card_biUnion_le_card_mul Kc inputs 2 hinputs
    _ = 2 * Kc.card := Nat.mul_comm _ _
