import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1194

open PEqualNP.CircuitLowerBounds

lemma ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def circuit : Circuit :=
  { gates :=
      [⟨GateOp.or, [1, 2]⟩,
       ⟨GateOp.or, [8, 3]⟩,
       ⟨GateOp.and, [0, 9]⟩,
       ⟨GateOp.or, [4, 5]⟩,
       ⟨GateOp.and, [1, 11]⟩,
       ⟨GateOp.or, [2, 7]⟩,
       ⟨GateOp.and, [6, 13]⟩,
       ⟨GateOp.or, [10, 12]⟩,
       ⟨GateOp.or, [15, 14]⟩],
    output := 16 }

lemma circuit_eval : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) ||
        (b && f) || (c && g) || (g && h)) := by
  decide

lemma circuit_monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1194

theorem PEqualNP.Outside.L_meta_1194 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) ||
          (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) ||
          (x 2 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1194.circuit,
    PEqualNP.Outside.L_meta_1194.circuit_monotone, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1194.ofFn8 x]
  exact PEqualNP.Outside.L_meta_1194.circuit_eval
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
