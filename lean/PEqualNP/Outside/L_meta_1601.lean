import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_1601 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro bound m H inst D hmono heval hgirth hclean
  classical
  have hNo4 : ∀ a b c d : Fin m, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    rintro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    let p : H.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hp : p.IsCycle := by
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      have hab' := hab.ne
      have hbc' := hbc.ne
      have hcd' := hcd.ne
      have hda' := hda.ne
      simp [p, Walk.isPath_def, hab', hbc', hcd', hda', hac, hbd,
        hab'.symm, hbc'.symm, hcd'.symm, hda'.symm, hac.symm, hbd.symm]
    have hh : 5 ≤ 4 := hgirth a p hp
    exact (by decide : ¬ (5 ≤ 4)) hh
  have hmono' : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    simpa only [Monotone2, Set.mem_insert_iff, Set.mem_singleton_iff] using hmono
  have heval' : ∀ x : Fin m → Bool,
      Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    simpa [circuitFun, graphFun] using congrFun heval x
  have hclean' : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = GateOp.and →
      (Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hop hv
    have hi : (gateAt D i.val).op = GateOp.and := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ i.isLt]
      exact hop
    have hv' : gateVal m D i.val x = true := hv
    have hx := hclean i.val i.isLt hi x hv'
    simpa [graphFun] using hx
  obtain ⟨S, hS, hsize⟩ := bound m H hNo4 D.gates D.output hmono' heval' hclean'
  exact ⟨S, hS, hsize, (Nat.le_add_right H.edgeFinset.card S.card).trans hsize⟩
